package integration

import (
	"time"

	abci "github.com/tendermint/tendermint/abci/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	"github.com/tendermint/tendermint/crypto/tmhash"
	tmtypes "github.com/tendermint/tendermint/types"
)

// TestHandleConsumerDoubleVoting verifies that handling a double voting evidence
// of a consumer chain results in the expected jailing and tombstoning of the malicious validator
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

	blockID1 := makeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := makeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

	vote1 := makeAndSignVote(
		blockID1,
		s.consumerCtx().BlockHeight(),
		s.consumerCtx().BlockTime(),
		valSet,
		signer,
		s.consumerChain.ChainID,
	)

	badVote := makeAndSignVote(
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
			"create infraction header using an invalid consumer chain id - shouldn't pass",
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
			// we create two votes that only differs by their Block IDs and
			// signed them using the same validator and chain ID of the consumer chain
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
		ctx := setDefaultConsensusEvidenceParams(s.providerCtx())
		s.Run(tc.name, func() {
			err = s.providerApp.GetProviderKeeper().HandleConsumerDoubleVoting(
				ctx,
				tc.ev,
				tc.chainID,
			)
			if tc.expPass {
				s.Require().NoError(err)

				// verifies that the jailing and tombstoning has occurred
				s.Require().True(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(ctx, provAddr.ToSdkConsAddr()))
				s.Require().True(s.providerApp.GetTestSlashingKeeper().IsTombstoned(ctx, provAddr.ToSdkConsAddr()))
			} else {
				s.Require().Error(err)

				// verifies that no jailing and tombstoning has occurred

				s.Require().False(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(ctx, provAddr.ToSdkConsAddr()))
				s.Require().False(s.providerApp.GetTestSlashingKeeper().IsTombstoned(ctx, provAddr.ToSdkConsAddr()))
			}
		})
	}
}

func (s *CCVTestSuite) TestVerifyDoubleVotingEvidence() {
	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	valSet, err := tmtypes.ValidatorSetFromProto(s.consumerChain.LastHeader.ValidatorSet)
	s.Require().NoError(err)

	val := valSet.Validators[0]
	signer := s.consumerChain.Signers[val.Address.String()]
	val2 := valSet.Validators[1]
	signer2 := s.consumerChain.Signers[val2.Address.String()]

	blockID1 := makeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := makeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

	oldTime := s.consumerCtx().BlockTime().Add(-505 * time.Hour)

	consuAddr := types.NewConsumerConsAddress(sdk.ConsAddress(val.Address.Bytes()))
	provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr)

	testCases := []struct {
		name    string
		votes   []*tmtypes.Vote
		chainID string
		expPass bool
	}{
		{
			"evidence is too old - shouldn't pass",
			[]*tmtypes.Vote{
				makeAndSignVote(
					blockID1,
					s.consumerCtx().BlockHeight(),
					oldTime,
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
				makeAndSignVote(
					blockID2,
					s.consumerCtx().BlockHeight(),
					oldTime,
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
			},
			s.consumerChain.ChainID,
			false,
		},
		{
			"evidence has votes with different block height - shouldn't pass",
			[]*tmtypes.Vote{
				makeAndSignVote(
					blockID1,
					s.consumerCtx().BlockHeight()+1,
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
				makeAndSignVote(
					blockID2,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
			},
			s.consumerChain.ChainID,
			false,
		},
		{
			"evidence has votes with different validator address - shouldn't pass",
			[]*tmtypes.Vote{
				makeAndSignVote(
					blockID1,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
				makeAndSignVote(
					blockID2,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer2,
					s.consumerChain.ChainID,
				),
			},
			s.consumerChain.ChainID,
			false,
		},
		{
			"evidence has votes with same block IDs - shouldn't pass",
			[]*tmtypes.Vote{
				makeAndSignVote(
					blockID1,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
				makeAndSignVote(
					blockID1,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
			},
			s.consumerChain.ChainID,
			false,
		},
		{
			"no consumer chain exists for the given chain ID - shouldn't pass",
			[]*tmtypes.Vote{
				makeAndSignVote(
					blockID1,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
				makeAndSignVote(
					blockID2,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
			},
			"WrongChainID",
			false,
		},
		{
			"voteA is signed using the wrong chain ID - shouldn't pass",
			[]*tmtypes.Vote{
				makeAndSignVote(
					blockID1,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					"WrongChainID",
				),
				makeAndSignVote(
					blockID2,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
			},
			s.consumerChain.ChainID,
			false,
		},
		{
			"voteB is signed using the wrong chain ID - shouldn't pass",
			[]*tmtypes.Vote{
				makeAndSignVote(
					blockID1,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
				makeAndSignVote(
					blockID2,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					"WrongChainID",
				),
			},
			s.consumerChain.ChainID,
			false,
		},
		{
			"valid double voting evidence should pass",
			[]*tmtypes.Vote{
				makeAndSignVote(
					blockID1,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
				makeAndSignVote(
					blockID2,
					s.consumerCtx().BlockHeight(),
					s.consumerCtx().BlockTime(),
					valSet,
					signer,
					s.consumerChain.ChainID,
				),
			},
			s.consumerChain.ChainID,
			true,
		},
	}

	for _, tc := range testCases {
		ctx := setDefaultConsensusEvidenceParams(s.providerCtx())
		s.Run(tc.name, func() {
			// get the consumer chain public key assigned to the validator
			consuPubkey, ok := s.providerApp.GetProviderKeeper().GetValidatorConsumerPubKey(
				ctx,
				s.consumerChain.ChainID,
				provAddr,
			)
			s.Require().True(ok)

			err := s.providerApp.GetProviderKeeper().VerifyDoubleVotingEvidence(
				ctx,
				tmtypes.DuplicateVoteEvidence{
					VoteA:            tc.votes[0],
					VoteB:            tc.votes[1],
					ValidatorPower:   val.VotingPower,
					TotalVotingPower: val.VotingPower,
					Timestamp:        tc.votes[0].Timestamp,
				},
				tc.chainID,
				consuPubkey,
			)
			if tc.expPass {
				s.Require().NoError(err)
			} else {
				s.Require().Error(err)
			}
		})
	}
}

// utility function duplicated from CometBFT
// see https://github.com/cometbft/cometbft/blob/main/evidence/verify_test.go#L554
func makeBlockID(hash []byte, partSetSize uint32, partSetHash []byte) tmtypes.BlockID {
	var (
		h   = make([]byte, tmhash.Size)
		psH = make([]byte, tmhash.Size)
	)
	copy(h, hash)
	copy(psH, partSetHash)
	return tmtypes.BlockID{
		Hash: h,
		PartSetHeader: tmtypes.PartSetHeader{
			Total: partSetSize,
			Hash:  psH,
		},
	}
}

func makeAndSignVote(
	blockID tmtypes.BlockID,
	blockHeight int64,
	blockTime time.Time,
	valSet *tmtypes.ValidatorSet,
	signer tmtypes.PrivValidator,
	chainID string,
) *tmtypes.Vote {
	vote, err := tmtypes.MakeVote(
		blockHeight,
		blockID,
		valSet,
		signer,
		chainID,
		blockTime,
	)
	if err != nil {
		panic(err)
	}

	v := vote.ToProto()
	err = signer.SignVote(chainID, v)
	if err != nil {
		panic(err)
	}

	vote.Signature = v.Signature
	return vote
}

func setDefaultConsensusEvidenceParams(ctx sdk.Context) sdk.Context {
	return ctx.WithConsensusParams(
		&abci.ConsensusParams{
			Evidence: &tmproto.EvidenceParams{
				MaxAgeNumBlocks: 302400,
				MaxAgeDuration:  504 * time.Hour, // 3 weeks is the max duration
				MaxBytes:        10000,
			},
		},
	)
}
