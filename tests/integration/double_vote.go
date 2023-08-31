package integration

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	testutil "github.com/cosmos/interchain-security/v2/testutil/crypto"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// TestHandleConsumerDoubleVoting verifies that handling a double voting evidence
// of a consumer chain results in the expected jailing of the malicious validator
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
	s.Require().NoError(err)
	consuSigner := s.consumerChain.Signers[consuVal.Address.String()]

	prvovValSet, err := tmtypes.ValidatorSetFromProto(s.providerChain.LastHeader.ValidatorSet)
	s.Require().NoError(err)
	prvovVal := prvovValSet.Validators[0]
	prvovSigner := s.providerChain.Signers[prvovVal.Address.String()]

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
		prvovValSet,
		prvovSigner,
		s.consumerChain.ChainID,
	)

	provBadVote := testutil.MakeAndSignVote(
		blockID2,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		prvovValSet,
		prvovSigner,
		s.consumerChain.ChainID,
	)

	testCases := []struct {
		name    string
		ev      *tmtypes.DuplicateVoteEvidence
		chainID string
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
			true,
		},
		{
			// create double voting evidence as if we didn't assign
			// a new key to the validator on the consumer chain
			"valid double voting evidence 2 - should pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            provVote,
				VoteB:            provBadVote,
				ValidatorPower:   consuVal.VotingPower,
				TotalVotingPower: consuVal.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			s.consumerChain.ChainID,
			true,
		},
	}

	// consumer and provider address of the validator
	consuAddr := types.NewConsumerConsAddress(sdk.ConsAddress(consuVal.Address.Bytes()))
	provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr)

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			// reset context for each run
			provCtx := s.providerCtx()

			// remove key assigned if the validator provider key is used
			if tc.ev.VoteA.ValidatorAddress.String() != consuVal.Address.String() {
				s.providerApp.GetProviderKeeper().DeleteKeyAssignments(provCtx, s.consumerChain.ChainID)
			}

			err = s.providerApp.GetProviderKeeper().HandleConsumerDoubleVoting(
				provCtx,
				tc.ev,
				tc.chainID,
			)

			if tc.expPass {
				s.Require().NoError(err)

				// verifies that the jailing has occurred
				s.Require().True(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(provCtx, provAddr.ToSdkConsAddr()))
			} else {
				s.Require().Error(err)

				// verifies that no jailing and has occurred
				s.Require().False(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(provCtx, provAddr.ToSdkConsAddr()))
			}
		})
	}
}
