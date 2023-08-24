package keeper_test

import (
	"testing"
	"time"

	testutil "github.com/cosmos/interchain-security/v2/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v2/testutil/keeper"
	"github.com/stretchr/testify/require"
	tmencoding "github.com/tendermint/tendermint/crypto/encoding"
	tmtypes "github.com/tendermint/tendermint/types"
)

func TestVerifyDoubleVotingEvidence(t *testing.T) {
	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := consumer

	signer1 := tmtypes.NewMockPV()
	signer2 := tmtypes.NewMockPV()

	val1 := tmtypes.NewValidator(signer1.PrivKey.PubKey(), 1)
	val2 := tmtypes.NewValidator(signer2.PrivKey.PubKey(), 1)

	valSet := tmtypes.NewValidatorSet([]*tmtypes.Validator{val1, val2})

	// valSet, err := tmtypes.ValidatorSetFromProto(s.consumerChain.LastHeader.ValidatorSet)
	// require.NoError(t, err)

	// val := valSet.Validators[0]
	// signer := s.consumerChain.Signers[val.Address.String()]
	// val2 := valSet.Validators[1]
	// signer2 := s.consumerChain.Signers[val2.Address.String()]

	blockID1 := testutil.MakeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := testutil.MakeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

	ctx = ctx.WithBlockTime(time.Now())
	oldTime := ctx.BlockTime().Add(-505 * time.Hour)

	testCases := []struct {
		name    string
		votes   []*tmtypes.Vote
		chainID string
		expPass bool
	}{
		{
			"evidence is too old - shouldn't pass",
			[]*tmtypes.Vote{
				testutil.MakeAndSignVote(
					blockID1,
					ctx.BlockHeight(),
					oldTime,
					valSet,
					signer1,
					chainID,
				),
				testutil.MakeAndSignVote(
					blockID2,
					ctx.BlockHeight(),
					oldTime,
					valSet,
					signer1,
					chainID,
				),
			},
			chainID,
			false,
		},
		{
			"evidence has votes with different block height - shouldn't pass",
			[]*tmtypes.Vote{
				testutil.MakeAndSignVote(
					blockID1,
					ctx.BlockHeight()+1,
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
				testutil.MakeAndSignVote(
					blockID2,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
			},
			chainID,
			false,
		},
		{
			"evidence has votes with different validator address - shouldn't pass",
			[]*tmtypes.Vote{
				testutil.MakeAndSignVote(
					blockID1,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
				testutil.MakeAndSignVote(
					blockID2,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer2,
					chainID,
				),
			},
			chainID,
			false,
		},
		{
			"evidence has votes with same block IDs - shouldn't pass",
			[]*tmtypes.Vote{
				testutil.MakeAndSignVote(
					blockID1,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
				testutil.MakeAndSignVote(
					blockID1,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
			},
			chainID,
			false,
		},
		{
			"no consumer chain exists for the given chain ID - shouldn't pass",
			[]*tmtypes.Vote{
				testutil.MakeAndSignVote(
					blockID1,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
				testutil.MakeAndSignVote(
					blockID2,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
			},
			"WrongChainID",
			false,
		},
		{
			"voteA is signed using the wrong chain ID - shouldn't pass",
			[]*tmtypes.Vote{
				testutil.MakeAndSignVote(
					blockID1,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					"WrongChainID",
				),
				testutil.MakeAndSignVote(
					blockID2,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
			},
			chainID,
			false,
		},
		{
			"voteB is signed using the wrong chain ID - shouldn't pass",
			[]*tmtypes.Vote{
				testutil.MakeAndSignVote(
					blockID1,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
				testutil.MakeAndSignVote(
					blockID2,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					"WrongChainID",
				),
			},
			chainID,
			false,
		},
		{
			"valid double voting evidence should pass",
			[]*tmtypes.Vote{
				testutil.MakeAndSignVote(
					blockID1,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
				testutil.MakeAndSignVote(
					blockID2,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
			},
			chainID,
			true,
		},
	}

	ctx = testutil.SetDefaultConsensusEvidenceParams(ctx)

	for _, tc := range testCases {
		// TODO: add test case when pukey is invalid
		consuPubkey, err := tmencoding.PubKeyToProto(val1.PubKey)
		require.NoError(t, err)

		err = keeper.VerifyDoubleVotingEvidence(
			ctx,
			tmtypes.DuplicateVoteEvidence{
				VoteA:            tc.votes[0],
				VoteB:            tc.votes[1],
				ValidatorPower:   val1.VotingPower,
				TotalVotingPower: val1.VotingPower,
				Timestamp:        tc.votes[0].Timestamp,
			},
			tc.chainID,
			consuPubkey,
		)
		if tc.expPass {
			require.NoError(t, err)
		} else {
			require.Error(t, err)
		}
	}

}
