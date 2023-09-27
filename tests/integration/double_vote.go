package integration

import (
	"bytes"

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

	// In what follows, we have the "valid double voting evidence 1 - should pass," and
	// "valid double voting evidence 2 - should pass" test cases. The first test case has valid double
	// voting evidence for the consumer chain (using a consumer key), while the second test case has valid double
	// voting evidence (using a provider key). When the first "valid double voting evidence 1 - should pass" test runs
	// it would slash the validator that corresponds to the consumer validator. If the second test
	// "valid double voting evidence 2 - should pass" attempts to slash the same validator, the test would fail
	// because the validator was already slashed in the first test case.
	// Depending on what `consuSigner` and the `provSigner` are, that are arbitrarily chosen, when we run the test, we
	// might have a successful or a failed test. To prevent a flaky test like this, in what follows we check that we find the
	// validator that corresponds to `consuVal` and then find a `provVal` validator that is not the corresponding
	// validator of `consuVal` on the provider chain. This way we guarantee that the test is not flaky.
	allValidators := s.providerApp.GetProviderKeeper().GetAllValidatorsByConsumerAddr(s.providerCtx(), &s.consumerChain.ChainID)
	consuValIndex := 0
	for i := 0; i < len(allValidators); i++ {
		if bytes.Equal(allValidators[i].ConsumerAddr, consuVal.Address.Bytes()) {
			consuValIndex = i
			break
		}
	}

	provValIndex := 0
	for i := 0; i < len(provValSet.Validators); i++ {
		if !bytes.Equal(allValidators[consuValIndex].ProviderAddr, provValSet.Validators[i].Address.Bytes()) {
			provValIndex = i
			break
		}
	}

	provVal := provValSet.Validators[provValIndex]
	provSigner := s.providerChain.Signers[provVal.Address.String()]

	blockID1 := testutil.MakeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := testutil.MakeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

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

	testCases := []struct {
		name    string
		ev      *tmtypes.DuplicateVoteEvidence
		chainID string
		pubkey  crypto.PubKey
		expPass bool
	}{
		{
			"invalid consumer chain id - shouldn't pass",
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

	consuAddr := types.NewConsumerConsAddress(sdk.ConsAddress(consuVal.Address.Bytes()))
	provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr)

	validator, _ := s.providerApp.GetTestStakingKeeper().GetValidator(s.providerCtx(), provAddr.ToSdkConsAddr().Bytes())
	initialTokens := validator.GetTokens().ToDec()
	for _, tc := range testCases {
		s.Run(tc.name, func() {
			// reset context for each run
			provCtx := s.providerCtx()

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
func (s *CCVTestSuite) TestHandleConsumerDoubleVotingSlashesUndelegations() {
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

	validator, found := s.providerApp.GetTestStakingKeeper().GetValidator(s.providerCtx(), provAddr.ToSdkConsAddr().Bytes())
	s.Require().True(found)

	s.Run("slash undelegations when getting double voting evidence", func() {
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

		_, shares, valAddr := delegateByIdx(s, delAddr, bondAmt, idx)
		_ = undelegate(s, delAddr, valAddr, shares)

		_, shares, _ = delegateByIdx(s, delAddr, sdk.NewInt(50000000), idx)
		_ = undelegate(s, delAddr, valAddr, shares)

		err = s.providerApp.GetProviderKeeper().HandleConsumerDoubleVoting(
			s.providerCtx(),
			evidence,
			chainID,
			pk,
		)
		s.Require().NoError(err)

		slashFraction := s.providerApp.GetTestSlashingKeeper().SlashFractionDoubleSign(s.providerCtx())

		// check undelegations are slashed
		ubds, _ := s.providerApp.GetTestStakingKeeper().GetUnbondingDelegation(s.providerCtx(), delAddr, validator.GetOperator())
		s.Require().True(len(ubds.Entries) > 0)
		for _, unb := range ubds.Entries {
			initialBalance := unb.InitialBalance.ToDec()
			currentBalance := unb.Balance.ToDec()
			s.Require().True(initialBalance.Sub(initialBalance.Mul(slashFraction)).Equal(currentBalance))
		}
	})
}
