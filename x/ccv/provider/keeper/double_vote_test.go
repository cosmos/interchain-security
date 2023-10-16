package keeper_test

import (
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	testutil "github.com/cosmos/interchain-security/v2/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v2/testutil/keeper"
	"github.com/stretchr/testify/require"
	tmtypes "github.com/tendermint/tendermint/types"
)

func TestVerifyDoubleVotingEvidence(t *testing.T) {
	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "consumer"

	signer1 := tmtypes.NewMockPV()
	signer2 := tmtypes.NewMockPV()

	val1 := tmtypes.NewValidator(signer1.PrivKey.PubKey(), 1)
	val2 := tmtypes.NewValidator(signer2.PrivKey.PubKey(), 1)

	valSet := tmtypes.NewValidatorSet([]*tmtypes.Validator{val1, val2})

	blockID1 := testutil.MakeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := testutil.MakeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

	ctx = ctx.WithBlockTime(time.Now())

	valPubkey1, err := cryptocodec.FromTmPubKeyInterface(val1.PubKey)
	require.NoError(t, err)

	valPubkey2, err := cryptocodec.FromTmPubKeyInterface(val2.PubKey)
	require.NoError(t, err)

	testCases := []struct {
		name    string
		votes   []*tmtypes.Vote
		chainID string
		pubkey  cryptotypes.PubKey
		expPass bool
	}{
		{
			"invalid verifying public key - shouldn't pass",
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
			nil,
			false,
		},
		{
			"verifying public key doesn't correspond to validator address",
			[]*tmtypes.Vote{
				testutil.MakeAndSignVoteWithForgedValAddress(
					blockID1,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
				testutil.MakeAndSignVoteWithForgedValAddress(
					blockID2,
					ctx.BlockHeight(),
					ctx.BlockTime(),
					valSet,
					signer1,
					chainID,
				),
			},
			chainID,
			valPubkey1,
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
			valPubkey1,
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
			valPubkey1,
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
			valPubkey1,
			false,
		},
		{
			"given chain ID isn't the same as the one used to sign the votes - shouldn't pass",
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
			valPubkey1,
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
			valPubkey1,
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
			valPubkey1,
			false,
		},
		{
			"wrong public key - shouldn't pass",
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
			valPubkey2,
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
			valPubkey1,
			true,
		},
	}

	for _, tc := range testCases {
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
			tc.pubkey,
		)
		if tc.expPass {
			require.NoError(t, err)
		} else {
			require.Error(t, err)
		}
	}
}
