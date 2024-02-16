package keeper_test

import (
	"fmt"
	abci "github.com/cometbft/cometbft/abci/types"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	"sort"
	"strings"
	"testing"
)

func TestHandleOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

	mocks.MockStakingKeeper.EXPECT().
		GetValidatorByConsAddr(gomock.Any(), gomock.Any()).
		DoAndReturn(func(ctx sdk.Context, addr sdk.ConsAddress) (stakingtypes.Validator, bool) {
			pkAny, _ := codectypes.NewAnyWithValue(ed25519.GenPrivKeyFromSecret([]byte{1}).PubKey())
			return stakingtypes.Validator{ConsensusPubkey: pkAny}, true
		}).AnyTimes()

	// trying to opt in to a non-proposed and non-registered chain returns an error
	require.Error(t, providerKeeper.HandleOptIn(ctx, "unknownChainID", providerAddr, nil))

	// if validator (`providerAddr`) is to be opted out, then we cancel that the validator is about
	// to be opted out and do not consider the validator to opt in
	providerKeeper.SetToBeOptedOut(ctx, "chainID", providerAddr)
	providerKeeper.SetProposedConsumerChain(ctx, "chainID", 1)
	require.True(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", providerAddr))
	providerKeeper.HandleOptIn(ctx, "chainID", providerAddr, nil)
	require.False(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", providerAddr))
	require.False(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", providerAddr))

	// if validator (`providerAddr`) is already opted in, then the validator cannot be opted in
	providerKeeper.SetOptedIn(ctx, "chainID", providerAddr, 1, 2)
	providerKeeper.HandleOptIn(ctx, "chainID", providerAddr, nil)
	require.False(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", providerAddr))
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
					return stakingtypes.Validator{ConsensusPubkey: pkAny, Status: stakingtypes.Bonded}, true
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

	// if validator (`providerAddr`) is to be opted in, then we cancel that the validator is about
	// to be opted out and do not consider the validator to opt out
	providerKeeper.SetToBeOptedIn(ctx, "chainID", providerAddr)
	providerKeeper.SetConsumerClientId(ctx, "chainID", "clientID")
	require.True(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", providerAddr))
	err := providerKeeper.HandleOptOut(ctx, "chainID", providerAddr)
	require.NoError(t, err)
	require.False(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", providerAddr))
	require.False(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", providerAddr))

	// if validator (`providerAddr`) is not opted in, then the validator cannot be opted out
	providerKeeper.DeleteOptedIn(ctx, "chainID", providerAddr)
	err = providerKeeper.HandleOptOut(ctx, "chainID", providerAddr)
	require.NoError(t, err)
	require.False(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", providerAddr))
}

func TestComputeValidatorUpdates(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create 10 validators, where the first 8 are bonded and the last 2 are unbonded
	var providerAddresses []types.ProviderConsAddress
	var pubKeys []tmprotocrypto.PublicKey
	for i := 0; i < 10; i++ {
		// generate a consensus public key for the provider
		providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{uint8(i)}).PubKey()
		consAddr := sdk.ConsAddress(providerConsPubKey.Address())
		providerAddr := types.NewProviderConsAddress(consAddr)
		providerAddresses = append(providerAddresses, providerAddr)

		var providerValidatorAddr sdk.ValAddress
		providerValidatorAddr = providerAddr.Address.Bytes()

		pkAny, _ := codectypes.NewAnyWithValue(providerConsPubKey)

		// all validators are bonded except the last 2
		status := stakingtypes.Bonded
		if i >= 8 {
			status = stakingtypes.Unbonded
		}

		validator := stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
			Status:          status,
		}

		pubKey, _ := validator.TmConsPublicKey()
		pubKeys = append(pubKeys, pubKey)

		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(ctx, consAddr).Return(validator, true).AnyTimes()

		mocks.MockStakingKeeper.EXPECT().
			GetLastValidatorPower(ctx, providerValidatorAddr).Return(int64(i)).AnyTimes()
	}

	// set first 6 validators as currently opted in where validators 1, 2, and 3 have a
	// different power now than the power they had when they opted in
	var currentValidators []keeper.OptedInValidator
	for i := 0; i < 6; i++ {
		if i > 0 && i < 4 {
			currentValidators = append(currentValidators,
				keeper.OptedInValidator{ProviderAddr: providerAddresses[i],
					BlockHeight: 1,
					Power:       uint64(i + 1)})
		} else {
			currentValidators = append(currentValidators,
				keeper.OptedInValidator{ProviderAddr: providerAddresses[i],
					BlockHeight: 1,
					Power:       uint64(i)})
		}
	}

	// remove the first 2 validators
	var validatorsToRemove []types.ProviderConsAddress
	for i := 0; i < 2; i++ {
		validatorsToRemove = append(validatorsToRemove, providerAddresses[i])
	}

	// add the last 4 validators
	var validatorsToAdd []types.ProviderConsAddress
	for i := 6; i < 10; i++ {
		validatorsToAdd = append(validatorsToAdd, providerAddresses[i])
	}

	expectedValUpdates := []abci.ValidatorUpdate{
		// validators 0 and 1 are removed and hence have a power of 0
		{PubKey: pubKeys[0], Power: 0},
		{PubKey: pubKeys[1], Power: 0},
		// validators 2 and 3 had a different power before and hence are also added with their latest power
		{PubKey: pubKeys[2], Power: 2},
		{PubKey: pubKeys[3], Power: 3},
		// validators 4, 5 are not added because their voting power did not change
		// validators 6 and 7 are bonded and are added
		{PubKey: pubKeys[6], Power: 6},
		{PubKey: pubKeys[7], Power: 7},
		// validators 8 and 9 are unbonded, so they are not added
	}

	actualValUpdates := providerKeeper.ComputeValidatorUpdates(ctx,
		currentValidators, validatorsToAdd, validatorsToRemove)

	sort.Slice(expectedValUpdates, func(i int, j int) bool {
		if expectedValUpdates[i].PubKey.Compare(expectedValUpdates[j].PubKey) < 0 {
			return true
		} else if expectedValUpdates[i].PubKey.Compare(expectedValUpdates[j].PubKey) == 0 {
			return expectedValUpdates[i].Power < expectedValUpdates[j].Power
		}
		return false
	})
	sort.Slice(actualValUpdates, func(i int, j int) bool {
		if actualValUpdates[i].PubKey.Compare(actualValUpdates[j].PubKey) < 0 {
			return true
		} else if actualValUpdates[i].PubKey.Compare(actualValUpdates[j].PubKey) == 0 {
			return actualValUpdates[i].Power < actualValUpdates[j].Power
		}
		return false
	})

	require.Equal(t, expectedValUpdates, actualValUpdates)

}

func TestComputeNextValidators(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// change the block height, so we can verify that newly added validators have the right height set
	ctx = ctx.WithBlockHeight(1000)

	// create 10 validators, where the first 8 are bonded and the last 2 are unbonded
	var providerAddresses []types.ProviderConsAddress
	var pubKeys []tmprotocrypto.PublicKey
	for i := 0; i < 10; i++ {
		// generate a consensus public key for the provider
		providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{uint8(i)}).PubKey()
		consAddr := sdk.ConsAddress(providerConsPubKey.Address())
		providerAddr := types.NewProviderConsAddress(consAddr)
		providerAddresses = append(providerAddresses, providerAddr)

		var providerValidatorAddr sdk.ValAddress
		providerValidatorAddr = providerAddr.Address.Bytes()

		pkAny, _ := codectypes.NewAnyWithValue(providerConsPubKey)

		// all validators are bonded except the last 2
		status := stakingtypes.Bonded
		if i >= 8 {
			status = stakingtypes.Unbonded
		}

		validator := stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
			Status:          status,
		}

		pubKey := tmprotocrypto.PublicKey{
			Sum: &tmprotocrypto.PublicKey_Ed25519{
				Ed25519: consAddr.Bytes(),
			},
		}
		pubKeys = append(pubKeys, pubKey)

		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(ctx, consAddr).Return(validator, true).AnyTimes()

		mocks.MockStakingKeeper.EXPECT().
			GetLastValidatorPower(ctx, providerValidatorAddr).Return(int64(i)).AnyTimes()

	}

	// set first 6 validators as currently opted in where validators 1, 2, and 3 have a
	// different power now than the power they had when they opted in
	var currentValidators []keeper.OptedInValidator
	for i := 0; i < 6; i++ {
		if i > 0 && i < 4 {
			currentValidators = append(currentValidators,
				keeper.OptedInValidator{ProviderAddr: providerAddresses[i],
					BlockHeight: 1,
					Power:       uint64(i + 1)})
		} else {
			currentValidators = append(currentValidators,
				keeper.OptedInValidator{ProviderAddr: providerAddresses[i],
					BlockHeight: 1,
					Power:       uint64(i)})
		}
	}

	// remove the first 2 validators
	var validatorsToRemove []types.ProviderConsAddress
	for i := 0; i < 2; i++ {
		validatorsToRemove = append(validatorsToRemove, providerAddresses[i])
	}

	// add the last 4 validators
	var validatorsToAdd []types.ProviderConsAddress
	for i := 6; i < 10; i++ {
		validatorsToAdd = append(validatorsToAdd, providerAddresses[i])
	}

	expectedValidators := []keeper.OptedInValidator{
		// validators 0 and 1 are removed
		// validators 2 to 5 are still opted in and hence remain
		{ProviderAddr: providerAddresses[2], BlockHeight: uint64(1), Power: uint64(2)},
		{ProviderAddr: providerAddresses[3], BlockHeight: uint64(1), Power: uint64(3)},
		{ProviderAddr: providerAddresses[4], BlockHeight: uint64(1), Power: uint64(4)},
		{ProviderAddr: providerAddresses[5], BlockHeight: uint64(1), Power: uint64(5)},
		// validators 6 and 7 are now opted in and hence have the latest `BlockHeight`
		{ProviderAddr: providerAddresses[6], BlockHeight: uint64(1000), Power: uint64(6)},
		{ProviderAddr: providerAddresses[7], BlockHeight: uint64(1000), Power: uint64(7)},
		// validators 8 and 9 are unbonded, so they are not added
	}

	actualValidators := providerKeeper.ComputeNextValidators(ctx,
		currentValidators, validatorsToAdd, validatorsToRemove)

	sort.Slice(actualValidators, func(i int, j int) bool {
		if strings.Compare(actualValidators[i].ProviderAddr.String(), actualValidators[j].ProviderAddr.String()) == 0 {
			if actualValidators[i].BlockHeight == actualValidators[j].BlockHeight {
				return actualValidators[i].Power < actualValidators[j].Power
			}
			return actualValidators[i].BlockHeight < actualValidators[j].BlockHeight
		}
		return strings.Compare(actualValidators[i].ProviderAddr.String(), actualValidators[j].ProviderAddr.String()) < 0
	})

	sort.Slice(expectedValidators, func(i int, j int) bool {
		if strings.Compare(expectedValidators[i].ProviderAddr.String(), expectedValidators[j].ProviderAddr.String()) == 0 {
			if expectedValidators[i].BlockHeight == expectedValidators[j].BlockHeight {
				return expectedValidators[i].Power < expectedValidators[j].Power
			}
			return expectedValidators[i].BlockHeight < expectedValidators[j].BlockHeight
		}
		return strings.Compare(expectedValidators[i].ProviderAddr.String(), expectedValidators[j].ProviderAddr.String()) < 0
	})

	require.Equal(t, expectedValidators, actualValidators)
}

func TestResetCurrentValidators(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	// create 10 provider addresses
	providerAddresses := make([]types.ProviderConsAddress, 10)
	for i := 0; i < 10; i++ {
		providerAddresses[i] = types.NewProviderConsAddress([]byte(fmt.Sprintf("providerAddr%d", i)))
	}

	// opt in the first 5 validators
	for i := 0; i < 5; i++ {
		providerKeeper.SetOptedIn(ctx, chainID, providerAddresses[i], 1, 1)
	}
	require.NotEmpty(t, providerKeeper.GetOptedIn(ctx, chainID))

	// set the remaining 5 validators as opted in
	nextValidators := []keeper.OptedInValidator{
		{ProviderAddr: providerAddresses[6], BlockHeight: uint64(6), Power: uint64(6)},
		{ProviderAddr: providerAddresses[7], BlockHeight: uint64(7), Power: uint64(7)},
		{ProviderAddr: providerAddresses[8], BlockHeight: uint64(8), Power: uint64(8)},
		{ProviderAddr: providerAddresses[9], BlockHeight: uint64(9), Power: uint64(9)},
	}

	providerKeeper.ResetCurrentValidators(ctx, chainID, nextValidators)

	require.Empty(t, providerKeeper.GetToBeOptedIn(ctx, chainID))
	require.Empty(t, providerKeeper.GetToBeOptedOut(ctx, chainID))

	// verify that the currently opted in validators (`actualValidators`) are the ones that were in `nextValidators`
	actualValidators := providerKeeper.GetOptedIn(ctx, chainID)

	sort.Slice(actualValidators, func(i int, j int) bool {
		if strings.Compare(actualValidators[i].ProviderAddr.String(), actualValidators[j].ProviderAddr.String()) == 0 {
			if actualValidators[i].BlockHeight == actualValidators[j].BlockHeight {
				return actualValidators[i].Power < actualValidators[j].Power
			}
			return actualValidators[i].BlockHeight < actualValidators[j].BlockHeight
		}
		return strings.Compare(actualValidators[i].ProviderAddr.String(), actualValidators[j].ProviderAddr.String()) < 0
	})

	sort.Slice(nextValidators, func(i int, j int) bool {
		if strings.Compare(nextValidators[i].ProviderAddr.String(), nextValidators[j].ProviderAddr.String()) == 0 {
			if nextValidators[i].BlockHeight == nextValidators[j].BlockHeight {
				return nextValidators[i].Power < nextValidators[j].Power
			}
			return nextValidators[i].BlockHeight < nextValidators[j].BlockHeight
		}
		return strings.Compare(nextValidators[i].ProviderAddr.String(), nextValidators[j].ProviderAddr.String()) < 0
	})

	require.Equal(t, nextValidators, actualValidators)
}
