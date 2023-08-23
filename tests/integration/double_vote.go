package integration

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	"github.com/tendermint/tendermint/crypto/tmhash"
	tmtypes "github.com/tendermint/tendermint/types"
)

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

	vote1, err := tmtypes.MakeVote(
		s.consumerCtx().BlockHeight(),
		blockID1,
		valSet,
		signer,
		s.consumerChain.ChainID,
		s.consumerCtx().BlockTime(),
	)

	s.Require().NoError(err)

	v1 := vote1.ToProto()
	err = signer.SignVote(s.consumerChain.ChainID, v1)
	s.Require().NoError(err)

	badVote, err := tmtypes.MakeVote(
		s.consumerCtx().BlockHeight(),
		blockID2,
		valSet,
		signer,
		s.consumerChain.ChainID,
		s.consumerCtx().BlockTime(),
	)

	s.Require().NoError(err)

	bv := badVote.ToProto()
	err = signer.SignVote(s.consumerChain.ChainID, bv)
	s.Require().NoError(err)

	evidence := &tmtypes.DuplicateVoteEvidence{
		VoteA:            vote1,
		VoteB:            badVote,
		ValidatorPower:   val.VotingPower,
		TotalVotingPower: val.VotingPower,
		Timestamp:        s.consumerCtx().BlockTime(),
	}

	vote1.Signature = v1.Signature
	badVote.Signature = bv.Signature

	err = s.providerApp.GetProviderKeeper().HandleConsumerDoubleVoting(s.providerCtx(), evidence, s.consumerChain.LastHeader)
	s.Require().NoError(err)

	consuAddr := types.NewConsumerConsAddress(sdk.ConsAddress(val.Address.Bytes()))
	provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr)
	s.Require().True(s.providerApp.GetTestStakingKeeper().IsValidatorJailed(s.providerCtx(), provAddr.ToSdkConsAddr()))
	s.Require().True(s.providerApp.GetTestSlashingKeeper().IsTombstoned(s.providerCtx(), provAddr.ToSdkConsAddr()))
}

func (s *CCVTestSuite) TestVerifyDoubleVoting() {
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

	consuAddr := types.NewConsumerConsAddress(sdk.ConsAddress(val.Address.Bytes()))
	provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr)

	testCases := []struct {
		name            string
		currBlockHeight int64
		providerAddr    types.ProviderConsAddress
		evTimestamp     time.Time
		votes           []*tmtypes.Vote
		chainID         string
		expPass         bool
	}{
		{
			"expired evidence - shouldn't pass",
			s.consumerCtx().BlockHeight() + 10000001,
			provAddr,
			s.consumerCtx().BlockTime(),
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
			false,
		},
		{
			"votes with different block height - shouldn't pass",
			s.consumerCtx().BlockHeight(),
			provAddr,
			s.consumerCtx().BlockTime(),
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
			"votes with different validator address - shouldn't pass",
			s.consumerCtx().BlockHeight(),
			provAddr,
			s.consumerCtx().BlockTime(),
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
			"votes with same block IDs - shouldn't pass",
			s.consumerCtx().BlockHeight(),
			provAddr,
			s.consumerCtx().BlockTime(),
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
			"no consumer chain for given chain ID - shouldn't pass",
			s.consumerCtx().BlockHeight(),
			provAddr,
			s.consumerCtx().BlockTime(),
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
			"voteA signed with wrong chain ID doesn't exist - shouldn't pass",
			s.consumerCtx().BlockHeight(),
			provAddr,
			s.consumerCtx().BlockTime(),
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
			"voteB signed with wrong chain ID - shouldn't pass",
			s.consumerCtx().BlockHeight(),
			provAddr,
			s.consumerCtx().BlockTime(),
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
			"valid evidence should pass",
			s.consumerCtx().BlockHeight(),
			provAddr,
			s.consumerCtx().BlockTime(),
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
		s.Run(tc.name, func() {
			ctx := s.providerCtx().WithBlockHeight(tc.currBlockHeight)
			err := s.providerApp.GetProviderKeeper().VerifyDoubleVoting(
				ctx,
				tmtypes.DuplicateVoteEvidence{
					VoteA:            tc.votes[0],
					VoteB:            tc.votes[1],
					ValidatorPower:   val.VotingPower,
					TotalVotingPower: val.VotingPower,
					Timestamp:        s.consumerCtx().BlockTime(),
				},
				tc.chainID,
				tc.providerAddr,
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
