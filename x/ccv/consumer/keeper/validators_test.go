package keeper_test

import (
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	tmrand "github.com/tendermint/tendermint/libs/rand"
	tmtypes "github.com/tendermint/tendermint/types"
)

// TestApplyCCValidatorChanges tests the ApplyCCValidatorChanges method for a consumer keeper
func TestApplyCCValidatorChanges(t *testing.T) {

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	// Explicitly register cdc with public key interface
	keeperParams.RegisterSdkCryptoCodecInterfaces()
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()

	// utility functions
	getCCVals := func() (vals []types.CrossChainValidator) {
		vals = consumerKeeper.GetAllCCValidator(ctx)
		return
	}

	clearCCVals := func() {
		ccVals := consumerKeeper.GetAllCCValidator(ctx)
		for _, v := range ccVals {
			consumerKeeper.DeleteCCValidator(ctx, v.Address)
		}
	}

	sumCCValsPow := func(vals []types.CrossChainValidator) (power int64) {
		for _, v := range vals {
			power += v.Power
		}
		return
	}

	// prepare the testing setup by clearing the current cross-chain validators in states
	clearCCVals()

	tcValidators := GenerateValidators(t)

	changes := []abci.ValidatorUpdate{}
	changesPower := int64(0)

	for _, v := range tcValidators {
		changes = append(changes, tmtypes.TM2PB.ValidatorUpdate(v))
		changesPower += v.VotingPower
	}

	// finish setup by storing 3 out 4 testing validators as cross-chain validator records
	SetCCValidators(t, consumerKeeper, ctx, tcValidators[:len(tcValidators)-1])

	// verify setup
	ccVals := getCCVals()
	require.Len(t, ccVals, len(tcValidators)-1)

	// test behaviors
	testCases := []struct {
		changes       []abci.ValidatorUpdate
		expTotalPower int64
		expValsNum    int
	}{{ // add new bonded validator
		changes:       changes[len(changes)-1:],
		expTotalPower: changesPower,
		expValsNum:    len(ccVals) + 1,
	}, { // update a validator voting power
		changes:       []abci.ValidatorUpdate{{PubKey: changes[0].PubKey, Power: changes[0].Power + 3}},
		expTotalPower: changesPower + 3,
		expValsNum:    len(ccVals) + 1,
	}, { // unbond a validator
		changes:       []abci.ValidatorUpdate{{PubKey: changes[0].PubKey, Power: 0}},
		expTotalPower: changesPower - changes[0].Power,
		expValsNum:    len(ccVals),
	},
		{ // update all validators voting power
			changes: []abci.ValidatorUpdate{
				{PubKey: changes[0].PubKey, Power: changes[0].Power + 1},
				{PubKey: changes[1].PubKey, Power: changes[1].Power + 2},
				{PubKey: changes[2].PubKey, Power: changes[2].Power + 3},
				{PubKey: changes[3].PubKey, Power: changes[3].Power + 4},
			},
			expTotalPower: changesPower + 10,
			expValsNum:    len(ccVals) + 1,
		},
	}

	for _, tc := range testCases {

		consumerKeeper.ApplyCCValidatorChanges(ctx, tc.changes)
		gotVals := getCCVals()

		require.Len(t, gotVals, tc.expValsNum)
		require.Equal(t, tc.expTotalPower, sumCCValsPow(gotVals))
	}
}

// Tests the getter and setter behavior for historical info
func TestHistoricalInfo(t *testing.T) {

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	// Explicitly register cdc with public key interface
	keeperParams.RegisterSdkCryptoCodecInterfaces()
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()
	ctx = ctx.WithBlockHeight(15)

	// Generate test validators, save them to store, and retrieve stored records
	validators := GenerateValidators(t)
	SetCCValidators(t, consumerKeeper, ctx, validators)
	ccValidators := consumerKeeper.GetAllCCValidator(ctx)
	require.Len(t, ccValidators, len(validators))

	// iterate over validators and convert them to staking type
	sVals := []stakingtypes.Validator{}
	for _, v := range ccValidators {
		pk, err := v.ConsPubKey()
		require.NoError(t, err)

		val, err := stakingtypes.NewValidator(nil, pk, stakingtypes.Description{})
		require.NoError(t, err)

		// set voting power to random value
		val.Tokens = sdk.TokensFromConsensusPower(tmrand.NewRand().Int64(), sdk.DefaultPowerReduction)
		sVals = append(sVals, val)
	}

	currentHeight := ctx.BlockHeight()

	// create and store historical info
	hi := stakingtypes.NewHistoricalInfo(ctx.BlockHeader(), sVals, sdk.DefaultPowerReduction)
	consumerKeeper.SetHistoricalInfo(ctx, currentHeight, &hi)

	// expect to get historical info
	recv, found := consumerKeeper.GetHistoricalInfo(ctx, currentHeight)
	require.True(t, found, "HistoricalInfo not found after set")
	require.Equal(t, hi, recv, "HistoricalInfo not equal")

	// verify that historical info valset has validators sorted in order
	require.True(t, IsValSetSorted(recv.Valset, sdk.DefaultPowerReduction), "HistoricalInfo validators is not sorted")
}

// IsValSetSorted reports whether valset is sorted.
func IsValSetSorted(data []stakingtypes.Validator, powerReduction sdk.Int) bool {
	n := len(data)
	for i := n - 1; i > 0; i-- {
		if stakingtypes.ValidatorsByVotingPower(data).Less(i, i-1, powerReduction) {
			return false
		}
	}
	return true
}

// Generates 4 test validators with non zero voting power
func GenerateValidators(t testing.TB) []*tmtypes.Validator {
	numValidators := 4
	validators := []*tmtypes.Validator{}
	for i := 0; i < numValidators; i++ {
		pubKey, err := testkeeper.GenPubKey()
		require.NoError(t, err)

		votingPower := int64(i + 1)
		validator := tmtypes.NewValidator(pubKey, votingPower)
		validators = append(validators, validator)
	}
	return validators
}

// Sets each input tmtypes.Validator as a types.CrossChainValidator in the consumer keeper store
func SetCCValidators(t testing.TB, consumerKeeper keeper.Keeper,
	ctx sdk.Context, validators []*tmtypes.Validator) {
	for _, v := range validators {
		publicKey, err := cryptocodec.FromTmPubKeyInterface(v.PubKey)
		require.NoError(t, err)

		ccv, err := types.NewCCValidator(v.Address, v.VotingPower, publicKey)
		require.NoError(t, err)
		consumerKeeper.SetCCValidator(ctx, ccv)
	}
}
