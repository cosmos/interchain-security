package keeper_test

import (
	"testing"

	abci "github.com/cometbft/cometbft/abci/types"
	tmtypes "github.com/cometbft/cometbft/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
)

func TestComputeConsumerTotalVotingPower(t *testing.T) {
	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	createVal := func(power int64) tmtypes.Validator {
		signer := tmtypes.NewMockPV()
		val := tmtypes.NewValidator(signer.PrivKey.PubKey(), power)
		return *val
	}

	chainID := "consumer"
	validatorsVotes := make([]abci.VoteInfo, 5)

	expTotalPower := int64(0)

	// create validators, opt them in and use them
	// to create block votes
	for i := 0; i < 5; i++ {
		val := createVal(int64(i))
		keeper.SetOptedIn(
			ctx,
			chainID,
			types.NewProviderConsAddress(sdk.ConsAddress(val.Address)),
			0,
		)

		validatorsVotes = append(
			validatorsVotes,
			abci.VoteInfo{
				Validator: abci.Validator{
					Address: val.Address,
					Power:   val.VotingPower,
				},
			},
		)

		expTotalPower += val.VotingPower
	}

	res := keeper.ComputeConsumerTotalVotingPower(
		ctx,
		chainID,
		validatorsVotes,
	)

	require.Equal(t, expTotalPower, res)
}
