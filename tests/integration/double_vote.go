package integration

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	testutil "github.com/cosmos/interchain-security/v2/testutil/crypto"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	"github.com/tendermint/tendermint/crypto"
	tmtypes "github.com/tendermint/tendermint/types"
)

// TestHandleConsumerDoubleVoting verifies that handling a double voting evidence
// of a consumer chain results in the expected tombstoning and jailing the misbehaved validator
func (s *CCVTestSuite) TestHandleConsumerDoubleVoting() {
	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	// create signing info for all validators
	for _, v := range s.providerChain.Vals.Validators {
		s.setDefaultValSigningInfo(*v)
	}

	consuValSet, err := tmtypes.ValidatorSetFromProto(s.consumerChain.LastHeader.ValidatorSet)
	s.Require().NoError(err)
	consuVal := consuValSet.Validators[0]
	consuSigner := s.consumerChain.Signers[consuVal.Address.String()]

	provValSet, err := tmtypes.ValidatorSetFromProto(s.providerChain.LastHeader.ValidatorSet)
	s.Require().NoError(err)

	provVal := provValSet.Validators[0]
	provSigner := s.providerChain.Signers[provVal.Address.String()]

	blockID1 := testutil.MakeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := testutil.MakeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

	// Set the equivocation evidence min height to the previous block height
	equivocationEvidenceMinHeight := uint64(s.consumerCtx().BlockHeight() - 1)
	s.providerApp.GetProviderKeeper().SetEquivocationEvidenceMinHeight(
		s.providerCtx(),
		s.consumerChain.ChainID,
		equivocationEvidenceMinHeight,
	)
	// Note that votes are signed along with the chain ID
	// see VoteSignBytes in https://github.com/cometbft/cometbft/blob/main/types/vote.go#L139

	// create two votes using the consumer validator key
	consuVote := testutil.MakeAndSignVote(
		blockID1,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		consuValSet,
		consuSigner,
		s.consumerChain.ChainID,
	)

	consuBadVote := testutil.MakeAndSignVote(
		blockID2,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		consuValSet,
		consuSigner,
		s.consumerChain.ChainID,
	)

	// create two votes using the provider validator key
	provVote := testutil.MakeAndSignVote(
		blockID1,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		provValSet,
		provSigner,
		s.consumerChain.ChainID,
	)

	provBadVote := testutil.MakeAndSignVote(
		blockID2,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		provValSet,
		provSigner,
		s.consumerChain.ChainID,
	)

	// create a vote using the consumer validator key
	// with block height that is smaller than the equivocation evidence min height
	consuVoteOld := testutil.MakeAndSignVote(
		blockID1,
		int64(equivocationEvidenceMinHeight-1),
		s.consumerCtx().BlockTime(),
		consuValSet,
		consuSigner,
		s.consumerChain.ChainID,
	)

	testCases := []struct {
		name    string
		ev      *tmtypes.DuplicateVoteEvidence
		chainID string
		pubkey  crypto.PubKey
		expPass bool
	}{
		{
			"cannot find consumer chain for the given chain ID - shouldn't pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            consuVote,
				VoteB:            consuBadVote,
				ValidatorPower:   consuVal.VotingPower,
				TotalVotingPower: consuVal.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			"chainID",
			consuVal.PubKey,
			false,
		},
		{
			"evidence is older than equivocation evidence min height - shouldn't pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            consuVoteOld,
				VoteB:            consuBadVote,
				ValidatorPower:   consuVal.VotingPower,
				TotalVotingPower: consuVal.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			s.consumerChain.ChainID,
			consuVal.PubKey,
			false,
		},
		{
			"the votes in the evidence are for different height - shouldn't pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            consuVote,
				VoteB:            consuVoteOld,
				ValidatorPower:   consuVal.VotingPower,
				TotalVotingPower: consuVal.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			s.consumerChain.ChainID,
			consuVal.PubKey,
			false,
		},
		{
			"wrong public key - shouldn't pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            consuVote,
				VoteB:            consuVote,
				ValidatorPower:   consuVal.VotingPower,
				TotalVotingPower: consuVal.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			s.consumerChain.ChainID,
			provVal.PubKey,
			false,
		},
		{
			// create an invalid evidence containing two identical votes
			"invalid double voting evidence with identical votes - shouldn't pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            consuVote,
				VoteB:            consuVote,
				ValidatorPower:   consuVal.VotingPower,
				TotalVotingPower: consuVal.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			s.consumerChain.ChainID,
			consuVal.PubKey,
			false,
		},
		{
			// In order to create an evidence for a consumer chain,
			// we create two votes that only differ by their Block IDs and
			// signed them using the same validator private key and chain ID
			// of the consumer chain
			"valid double voting evidence 1 - should pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            consuVote,
				VoteB:            consuBadVote,
				ValidatorPower:   consuVal.VotingPower,
				TotalVotingPower: consuVal.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			s.consumerChain.ChainID,
			consuVal.PubKey,
			true,
		},
		{
			// create a double voting evidence using the provider validator key
			"valid double voting evidence 2 - should pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            provVote,
				VoteB:            provBadVote,
				ValidatorPower:   consuVal.VotingPower,
				TotalVotingPower: consuVal.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			s.consumerChain.ChainID,
			provVal.PubKey,
			true,
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			consuAddr := types.NewConsumerConsAddress(sdk.ConsAddress(tc.ev.VoteA.ValidatorAddress.Bytes()))
			provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr)

			validator, _ := s.providerApp.GetTestStakingKeeper().GetValidator(s.providerCtx(), provAddr.ToSdkConsAddr().Bytes())
			initialTokens := validator.GetTokens().ToDec()

			// reset context for each run
			provCtx, _ := s.providerCtx().CacheContext()

			// if the evidence was built using the validator provider address and key,
			// we remove the consumer key assigned to the validator otherwise
			// HandleConsumerDoubleVoting uses the consumer key to verify the signature
			if tc.ev.VoteA.ValidatorAddress.String() != consuVal.Address.String() {
				s.providerApp.GetProviderKeeper().DeleteKeyAssignments(provCtx, s.consumerChain.ChainID)
			}

			// convert validator public key
			pk, err := cryptocodec.FromTmPubKeyInterface(tc.pubkey)
			s.Require().NoError(err)

			err = s.providerApp.GetProviderKeeper().HandleConsumerDoubleVoting(
				provCtx,
				tc.ev,
				tc.chainID,
				pk,
			)

			if tc.expPass {
				s.Require().NoError(err)

				// verifies that the jailing and tombstoning has occurred
				s.Require().True(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(provCtx, provAddr.ToSdkConsAddr()))
				s.Require().True(s.providerApp.GetTestSlashingKeeper().IsTombstoned(provCtx, provAddr.ToSdkConsAddr()))

				// verifies that the val gets slashed and has fewer tokens after the slashing
				val, _ := s.providerApp.GetTestStakingKeeper().GetValidator(provCtx, provAddr.ToSdkConsAddr().Bytes())
				slashFraction := s.providerApp.GetTestSlashingKeeper().SlashFractionDoubleSign(provCtx)
				actualTokens := val.GetTokens().ToDec()
				s.Require().True(initialTokens.Sub(initialTokens.Mul(slashFraction)).Equal(actualTokens))
			} else {
				s.Require().Error(err)

				// verifies that no jailing and no tombstoning has occurred
				s.Require().False(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(provCtx, provAddr.ToSdkConsAddr()))
				s.Require().False(s.providerApp.GetTestSlashingKeeper().IsTombstoned(provCtx, provAddr.ToSdkConsAddr()))
			}
		})
	}
}

// TestHandleConsumerDoubleVotingSlashesUndelegations verifies that handling a successful double voting
// evidence of a consumer chain results in the expected slashing of the misbehave validator undelegations
func (s *CCVTestSuite) TestHandleConsumerDoubleVotingSlashesUndelegationsAndRelegations() {
	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	// create signing info for all validators
	for _, v := range s.providerChain.Vals.Validators {
		s.setDefaultValSigningInfo(*v)
	}

	consuValSet, err := tmtypes.ValidatorSetFromProto(s.consumerChain.LastHeader.ValidatorSet)
	s.Require().NoError(err)
	consuVal := consuValSet.Validators[0]
	consuVal2 := consuValSet.Validators[1]
	consuSigner := s.consumerChain.Signers[consuVal.Address.String()]

	blockID1 := testutil.MakeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := testutil.MakeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

	// create two votes using the consumer validator key
	consuVote := testutil.MakeAndSignVote(
		blockID1,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		consuValSet,
		consuSigner,
		s.consumerChain.ChainID,
	)

	consuBadVote := testutil.MakeAndSignVote(
		blockID2,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		consuValSet,
		consuSigner,
		s.consumerChain.ChainID,
	)

	// In order to create an evidence for a consumer chain,
	// we create two votes that only differ by their Block IDs and
	// signed them using the same validator private key and chain ID
	// of the consumer chain
	evidence := &tmtypes.DuplicateVoteEvidence{
		VoteA:            consuVote,
		VoteB:            consuBadVote,
		ValidatorPower:   consuVal.VotingPower,
		TotalVotingPower: consuVal.VotingPower,
		Timestamp:        s.consumerCtx().BlockTime(),
	}

	chainID := s.consumerChain.ChainID
	pubKey := consuVal.PubKey

	consuAddr := types.NewConsumerConsAddress(sdk.ConsAddress(consuVal.Address.Bytes()))
	provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr)

	consuAddr2 := types.NewConsumerConsAddress(sdk.ConsAddress(consuVal2.Address.Bytes()))
	provAddr2 := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr2)

	validator, found := s.providerApp.GetTestStakingKeeper().GetValidator(s.providerCtx(), provAddr.ToSdkConsAddr().Bytes())
	s.Require().True(found)

	validator2, found := s.providerApp.GetTestStakingKeeper().GetValidator(s.providerCtx(), provAddr2.ToSdkConsAddr().Bytes())
	s.Require().True(found)

	s.Run("slash undelegations and redelegations when getting double voting evidence", func() {
		// convert validator public key
		pk, err := cryptocodec.FromTmPubKeyInterface(pubKey)
		s.Require().NoError(err)

		// perform a delegation and an undelegation of the whole amount
		bondAmt := sdk.NewInt(10000000)
		delAddr := s.providerChain.SenderAccount.GetAddress()

		// in order to perform a delegation we need to know the validator's `idx` (that might not be 0)
		// loop through all validators to find the right `idx`
		idx := 0
		for i := 0; i <= len(s.providerChain.Vals.Validators); i++ {
			_, valAddr := s.getValByIdx(i)
			if validator.OperatorAddress == valAddr.String() {
				idx = i
				break
			}
		}

		// delegate bond amount
		_, shares, _ := delegateByIdx(s, delAddr, bondAmt, idx)
		s.Require().NotZero(shares)

		// undelegate 1/2 of the bound amount
		undelegate(s, delAddr, validator.GetOperator(), shares.Quo(sdk.NewDec(4)))
		undelegate(s, delAddr, validator.GetOperator(), shares.Quo(sdk.NewDec(4)))

		// check that undelegations was successful
		ubds, _ := s.providerApp.GetTestStakingKeeper().GetUnbondingDelegation(s.providerCtx(), delAddr, validator.GetOperator())
		// should have a single entry since undelegations are merged
		s.Require().Len(ubds.Entries, 1)

		// save the delegation shares of the validator to redelegate to
		// Note this shares should not be slashed!
		delShares := s.providerApp.GetTestStakingKeeper().Delegation(s.providerCtx(), delAddr, validator2.GetOperator()).GetShares()

		// redelegate 1/2 of the bound amount
		redelegate(s, delAddr, validator.GetOperator(), validator2.GetOperator(), shares.Quo(sdk.NewDec(4)))
		redelegate(s, delAddr, validator.GetOperator(), validator2.GetOperator(), shares.Quo(sdk.NewDec(4)))

		// check that redelegation was successful
		rdel := s.providerApp.GetTestStakingKeeper().GetRedelegations(s.providerCtx(), delAddr, uint16(10))
		s.Require().Len(rdel[0].Entries, 2)

		redelShares := rdel[0].Entries[0].SharesDst.Add(rdel[0].Entries[1].SharesDst)

		// cause double voting
		err = s.providerApp.GetProviderKeeper().HandleConsumerDoubleVoting(
			s.providerCtx(),
			evidence,
			chainID,
			pk,
		)
		s.Require().NoError(err)

		slashFraction := s.providerApp.GetTestSlashingKeeper().SlashFractionDoubleSign(s.providerCtx())

		// check undelegations and redelegations are slashed
		ubds, _ = s.providerApp.GetTestStakingKeeper().GetUnbondingDelegation(s.providerCtx(), delAddr, validator.GetOperator())

		s.Require().True(len(ubds.Entries) > 0)
		for _, unb := range ubds.Entries {
			initialBalance := unb.InitialBalance.ToDec()
			currentBalance := unb.Balance.ToDec()
			s.Require().True(initialBalance.Sub(initialBalance.Mul(slashFraction)).Equal(currentBalance))
		}

		delegations := s.providerApp.GetTestStakingKeeper().Delegation(s.providerCtx(), delAddr, validator2.GetOperator())
		s.Require().Equal(delegations.GetShares(), delShares.Add(redelShares).Sub(redelShares.Mul(slashFraction)))
	})
}
