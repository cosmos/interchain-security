package keeper_test

import (
	"bytes"
	"sort"
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

func TestHandleOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

	// trying to opt in to a non-proposed and non-registered chain returns an error
	require.Error(t, providerKeeper.HandleOptIn(ctx, "unknownChainID", providerAddr, nil))

	providerKeeper.SetProposedConsumerChain(ctx, "chainID", 1)
	require.False(t, providerKeeper.IsOptedIn(ctx, "chainID", providerAddr))
	providerKeeper.HandleOptIn(ctx, "chainID", providerAddr, nil)
	require.True(t, providerKeeper.IsOptedIn(ctx, "chainID", providerAddr))
}

func TestHandleOptInWithConsumerKey(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// generate a consensus public key for the provider
	providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{1}).PubKey()
	consAddr := sdk.ConsAddress(providerConsPubKey.Address())
	providerAddr := types.NewProviderConsAddress(consAddr)

	calls := []*gomock.Call{
		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(gomock.Any(), gomock.Any()).
			DoAndReturn(func(ctx sdk.Context, addr sdk.ConsAddress) (stakingtypes.Validator, bool) {
				if addr.Equals(providerAddr.Address) {
					// Given `providerAddr`, `GetValidatorByConsAddr` returns a validator with the
					// exact same `ConsensusPubkey`
					pkAny, _ := codectypes.NewAnyWithValue(providerConsPubKey)
					return stakingtypes.Validator{ConsensusPubkey: pkAny}, true
				} else {
					// for any other consensus address, we cannot find a validator
					return stakingtypes.Validator{}, false
				}
			}).Times(2),
	}

	gomock.InOrder(calls...)
	providerKeeper.SetProposedConsumerChain(ctx, "chainID", 1)

	// create a sample consumer key to assign to the `providerAddr` validator
	// on the consumer chain with id `chainID`
	consumerKey := "{\"@type\":\"/cosmos.crypto.ed25519.PubKey\",\"key\":\"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is=\"}"
	expectedConsumerPubKey, _ := providerKeeper.ParseConsumerKey(consumerKey)

	err := providerKeeper.HandleOptIn(ctx, "chainID", providerAddr, &consumerKey)
	require.NoError(t, err)

	// assert that the consumeKey was assigned to `providerAddr` validator on chain with id `chainID`
	actualConsumerPubKey, found := providerKeeper.GetValidatorConsumerPubKey(ctx, "chainID", providerAddr)
	require.True(t, found)
	require.Equal(t, expectedConsumerPubKey, actualConsumerPubKey)

	// assert that the `consumerAddr` to `providerAddr` association was set as well
	consumerAddr, _ := ccvtypes.TMCryptoPublicKeyToConsAddr(actualConsumerPubKey)
	actualProviderConsAddr, found := providerKeeper.GetValidatorByConsumerAddr(ctx, "chainID", types.NewConsumerConsAddress(consumerAddr))
	require.Equal(t, providerAddr, actualProviderConsAddr)
}

func TestHandleOptOut(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

	// trying to opt out from a not running chain returns an error
	require.Error(t, providerKeeper.HandleOptOut(ctx, "unknownChainID", providerAddr))

	// set a consumer client so that the chain is considered running
	providerKeeper.SetConsumerClientId(ctx, "chainID", "clientID")

	// if validator (`providerAddr`) is already opted in, then an opt-out would remove this validator
	providerKeeper.SetOptedIn(ctx, "chainID", providerAddr)
	require.True(t, providerKeeper.IsOptedIn(ctx, "chainID", providerAddr))
	providerKeeper.HandleOptOut(ctx, "chainID", providerAddr)
	require.False(t, providerKeeper.IsOptedIn(ctx, "chainID", providerAddr))
}

func TestHandleSetConsumerCommissionRate(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

	// trying to set a commission rate to a unknown consumer chain
	require.Error(t, providerKeeper.HandleSetConsumerCommissionRate(ctx, "unknownChainID", providerAddr, sdk.ZeroDec()))

	// setup a pending consumer chain
	chainID := "pendingChainID"
	providerKeeper.SetPendingConsumerAdditionProp(ctx, &types.ConsumerAdditionProposal{ChainId: chainID})

	// check that there's no commission rate set for the validator yet
	_, found := providerKeeper.GetConsumerCommissionRate(ctx, chainID, providerAddr)
	require.False(t, found)

	require.NoError(t, providerKeeper.HandleSetConsumerCommissionRate(ctx, chainID, providerAddr, sdk.OneDec()))

	// check that the commission rate is now set
	cr, found := providerKeeper.GetConsumerCommissionRate(ctx, chainID, providerAddr)
	require.Equal(t, sdk.OneDec(), cr)
	require.True(t, found)
}

func TestOptInTopNValidators(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create 4 validators with powers 1, 2, 3, and 1 respectively
	valA := createStakingValidator(ctx, mocks, 1, 1)
	valAConsAddr, _ := valA.GetConsAddr()
	valB := createStakingValidator(ctx, mocks, 2, 2)
	valBConsAddr, _ := valB.GetConsAddr()
	valC := createStakingValidator(ctx, mocks, 3, 3)
	valCConsAddr, _ := valC.GetConsAddr()
	valD := createStakingValidator(ctx, mocks, 4, 1)
	valDConsAddr, _ := valD.GetConsAddr()

	// Start Test 1: opt in all validators with power >= 0
	providerKeeper.OptInTopNValidators(ctx, "chainID", []stakingtypes.Validator{valA, valB, valC, valD}, 0)
	expectedOptedInValidators := []types.ProviderConsAddress{
		types.NewProviderConsAddress(valAConsAddr),
		types.NewProviderConsAddress(valBConsAddr),
		types.NewProviderConsAddress(valCConsAddr),
		types.NewProviderConsAddress(valDConsAddr)}
	actualOptedInValidators := providerKeeper.GetAllOptedIn(ctx, "chainID")

	// sort validators first to be able to compare
	sortUpdates := func(addresses []types.ProviderConsAddress) {
		sort.Slice(addresses, func(i, j int) bool {
			return bytes.Compare(addresses[i].ToSdkConsAddr(), addresses[j].ToSdkConsAddr()) < 0
		})
	}

	sortUpdates(expectedOptedInValidators)
	sortUpdates(actualOptedInValidators)
	require.Equal(t, expectedOptedInValidators, actualOptedInValidators)

	// reset state for the upcoming checks
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valAConsAddr))
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valBConsAddr))
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valCConsAddr))
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valDConsAddr))

	// Start Test 2: opt in all validators with power >= 1
	// We expect the same `expectedOptedInValidators` as when we opted in all validators with power >= 0 because the
	// validators with the smallest power have power == 1
	providerKeeper.OptInTopNValidators(ctx, "chainID", []stakingtypes.Validator{valA, valB, valC, valD}, 0)
	actualOptedInValidators = providerKeeper.GetAllOptedIn(ctx, "chainID")
	sortUpdates(actualOptedInValidators)
	require.Equal(t, expectedOptedInValidators, actualOptedInValidators)

	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valAConsAddr))
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valBConsAddr))
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valCConsAddr))
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valDConsAddr))

	// Start Test 3: opt in all validators with power >= 2 and hence we do not expect to opt in validator A
	providerKeeper.OptInTopNValidators(ctx, "chainID", []stakingtypes.Validator{valA, valB, valC, valD}, 2)
	expectedOptedInValidators = []types.ProviderConsAddress{
		types.NewProviderConsAddress(valBConsAddr),
		types.NewProviderConsAddress(valCConsAddr)}
	actualOptedInValidators = providerKeeper.GetAllOptedIn(ctx, "chainID")

	// sort validators first to be able to compare
	sortUpdates(expectedOptedInValidators)
	sortUpdates(actualOptedInValidators)
	require.Equal(t, expectedOptedInValidators, actualOptedInValidators)

	// reset state for the upcoming checks
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valAConsAddr))
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valBConsAddr))
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valCConsAddr))
	providerKeeper.DeleteOptedIn(ctx, "chainID", types.NewProviderConsAddress(valDConsAddr))

	// Start Test 4: opt in all validators with power >= 4 and hence we do not expect any opted-in validators
	providerKeeper.OptInTopNValidators(ctx, "chainID", []stakingtypes.Validator{valA, valB, valC, valD}, 4)
	require.Empty(t, providerKeeper.GetAllOptedIn(ctx, "chainID"))
}

func TestComputeMinPowerToOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create 5 validators with powers 1, 3, 5, 6, 10 (not in that order) with total power of 25 (= 1 + 3 + 5 + 6 + 10)
	// such that:
	// validator power => cumulative share
	// 10 => 40%
	// 6 => 64%
	// 5 => 84%
	// 3 => 96%
	// 1 => 100%

	bondedValidators := []stakingtypes.Validator{
		createStakingValidator(ctx, mocks, 1, 5),
		createStakingValidator(ctx, mocks, 2, 10),
		createStakingValidator(ctx, mocks, 3, 3),
		createStakingValidator(ctx, mocks, 4, 1),
		createStakingValidator(ctx, mocks, 5, 6),
	}

	require.Equal(t, int64(1), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 100))
	require.Equal(t, int64(1), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 97))
	require.Equal(t, int64(3), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 96))
	require.Equal(t, int64(3), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 85))
	require.Equal(t, int64(5), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 84))
	require.Equal(t, int64(5), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 65))
	require.Equal(t, int64(6), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 64))
	require.Equal(t, int64(6), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 41))
	require.Equal(t, int64(10), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 40))
	require.Equal(t, int64(10), providerKeeper.ComputeMinPowerToOptIn(ctx, bondedValidators, 1))
}

// TestShouldConsiderOnlyOptIn returns true if `validator` is opted in, in `chainID.
func TestShouldConsiderOnlyOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator := createStakingValidator(ctx, mocks, 0, 1)
	consAddr, _ := validator.GetConsAddr()

	require.False(t, providerKeeper.IsOptedIn(ctx, "chainID", types.NewProviderConsAddress(consAddr)))
	providerKeeper.SetOptedIn(ctx, "chainID", types.NewProviderConsAddress(consAddr))
	require.True(t, providerKeeper.IsOptedIn(ctx, "chainID", types.NewProviderConsAddress(consAddr)))

}
