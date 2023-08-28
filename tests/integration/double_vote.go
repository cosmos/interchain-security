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

	valSet, err := tmtypes.ValidatorSetFromProto(s.consumerChain.LastHeader.ValidatorSet)
	s.Require().NoError(err)

	val := valSet.Validators[0]
	signer := s.consumerChain.Signers[val.Address.String()]

	blockID1 := testutil.MakeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := testutil.MakeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

	// Note that votes are signed along with the chain ID
	// see VoteSignBytes in https://github.com/cometbft/cometbft/blob/main/types/vote.go#L139
	vote1 := testutil.MakeAndSignVote(
		blockID1,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		valSet,
		signer,
		s.consumerChain.ChainID,
	)

	badVote := testutil.MakeAndSignVote(
		blockID2,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		valSet,
		signer,
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
				VoteA:            vote1,
				VoteB:            badVote,
				ValidatorPower:   val.VotingPower,
				TotalVotingPower: val.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			"chainID",
			false,
		},
		{
			// create an invalid evidence containing two identical votes
			"invalid double voting evidence - shouldn't pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            vote1,
				VoteB:            vote1,
				ValidatorPower:   val.VotingPower,
				TotalVotingPower: val.VotingPower,
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
			"valid double voting evidence - should pass",
			&tmtypes.DuplicateVoteEvidence{
				VoteA:            vote1,
				VoteB:            badVote,
				ValidatorPower:   val.VotingPower,
				TotalVotingPower: val.VotingPower,
				Timestamp:        s.consumerCtx().BlockTime(),
			},
			s.consumerChain.ChainID,
			true,
		},
	}

	consuAddr := types.NewConsumerConsAddress(sdk.ConsAddress(val.Address.Bytes()))
	provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr)

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			err = s.providerApp.GetProviderKeeper().HandleConsumerDoubleVoting(
				s.providerCtx(),
				tc.ev,
				tc.chainID,
			)
			if tc.expPass {
				s.Require().NoError(err)

				// verifies that the jailing has occurred
				s.Require().True(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(s.providerCtx(), provAddr.ToSdkConsAddr()))
			} else {
				s.Require().Error(err)

				// verifies that no jailing and has occurred
				s.Require().False(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(s.providerCtx(), provAddr.ToSdkConsAddr()))
			}
		})
	}
}
