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

	provValSet, err := tmtypes.ValidatorSetFromProto(s.providerChain.LastHeader.ValidatorSet)
	s.Require().NoError(err)
	provVal := provValSet.Validators[0]
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

				// verifies that the tombstoning and jailing has occurred
				s.Require().True(s.providerApp.GetTestSlashingKeeper().IsTombstoned(provCtx, provAddr.ToSdkConsAddr()))
				s.Require().True(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(provCtx, provAddr.ToSdkConsAddr()))
			} else {
				s.Require().Error(err)

				// verifies that no jailing and has occurred
				s.Require().False(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(provCtx, provAddr.ToSdkConsAddr()))
			}
		})
	}
}
