package keeper_test

import (
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

func TestGetToBeOptedInValidators(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	var expectedAddresses []types.ProviderConsAddress
	// set 10 validators as to-be-opted-in, but only 3 (= 10/3) of those are `Bonded`
	for i := int64(0); i < 10; i++ {
		// generate a consensus public key for the provider
		providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{uint8(i)}).PubKey()
		consAddr := sdk.ConsAddress(providerConsPubKey.Address())
		providerAddr := types.NewProviderConsAddress(consAddr)

		var providerValidatorAddr sdk.ValAddress
		providerValidatorAddr = providerAddr.Address.Bytes()

		var status stakingtypes.BondStatus
		if i%3 == 0 {
			status = stakingtypes.Unbonded
		} else if i%3 == 1 {
			status = stakingtypes.Bonded
			// we only expect bonded validators to be returned by `GetToBeOptedInValidators`
			expectedAddresses = append(expectedAddresses, providerAddr)
		} else {
			status = stakingtypes.Unbonding
		}

		pkAny, _ := codectypes.NewAnyWithValue(providerConsPubKey)
		validator := stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
			Status:          status,
		}

		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(ctx, consAddr).Return(validator, true).AnyTimes()

		providerKeeper.SetToBeOptedIn(ctx, chainID, providerAddr)
	}

	actualAddresses := providerKeeper.GetToBeOptedInValidators(ctx, chainID)

	// sort before comparing
	sort.Slice(expectedAddresses, func(i int, j int) bool {
		return strings.Compare(expectedAddresses[i].String(), expectedAddresses[j].String()) < 0
	})
	sort.Slice(actualAddresses, func(i int, j int) bool {
		return strings.Compare(actualAddresses[i].String(), actualAddresses[j].String()) < 0
	})
	require.Equal(t, expectedAddresses, actualAddresses)
}

func TestGetNextOptedInValidators(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	// create 10 validators
	var providerAddresses []types.ProviderConsAddress
	for i := 0; i < 10; i++ {
		// generate a consensus public key for the provider
		providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{uint8(i)}).PubKey()
		consAddr := sdk.ConsAddress(providerConsPubKey.Address())
		providerAddr := types.NewProviderConsAddress(consAddr)
		providerAddresses = append(providerAddresses, providerAddr)

		var providerValidatorAddr sdk.ValAddress
		providerValidatorAddr = providerAddr.Address.Bytes()

		pkAny, _ := codectypes.NewAnyWithValue(providerConsPubKey)
		validator := stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
			Status:          stakingtypes.Bonded,
		}

		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(ctx, consAddr).Return(validator, true).AnyTimes()

		mocks.MockStakingKeeper.EXPECT().
			GetLastValidatorPower(ctx, providerValidatorAddr).Return(int64(i)).AnyTimes()
	}

	// first 3 validators (i.e., 0, 1, and 2) are already opted in but with the same power as they currently have
	// and therefore should not be returned by `GetNextOptedInValidators`
	for i := 0; i < 3; i++ {
		providerKeeper.SetOptedIn(ctx, chainID, providerAddresses[i], 1, uint64(i))

	}

	// validators 3, 4, 5 and 6 are already opted in but with a different voting power
	// and therefore should be returned by `GetNextOptedInValidators` (unless opted out -- see below)
	for i := 3; i < 7; i++ {
		providerKeeper.SetOptedIn(ctx, chainID, providerAddresses[i], 1, uint64(i+1))
	}

	// validators 8 and 9 are to be opted in
	for i := 8; i < 10; i++ {
		providerKeeper.SetToBeOptedIn(ctx, chainID, providerAddresses[i])
	}

	// first 5 validators are to be opted out and hence validators 3 and 4 won't be returned
	// by `GetNextOptedInValidators`
	for i := 0; i < 5; i++ {
		providerKeeper.SetToBeOptedOut(ctx, chainID, providerAddresses[i])
	}

	expectedAddresses := []types.ProviderConsAddress{
		providerAddresses[5],
		providerAddresses[6],
		providerAddresses[8],
		providerAddresses[9],
	}
	actualAddresses := providerKeeper.GetNextOptedInValidators(ctx, chainID)

	// sort before comparing
	sort.Slice(expectedAddresses, func(i int, j int) bool {
		return strings.Compare(expectedAddresses[i].String(), expectedAddresses[j].String()) < 0
	})
	sort.Slice(actualAddresses, func(i int, j int) bool {
		return strings.Compare(actualAddresses[i].String(), actualAddresses[j].String()) < 0
	})
	require.Equal(t, expectedAddresses, actualAddresses)
}

func TestComputePartialSetValidatorUpdates(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create 10 validators
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
		validator := stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
			Status:          stakingtypes.Bonded,
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

	// first 6 validators to opt in
	var nextOptedIn []types.ProviderConsAddress
	for i := 0; i < 6; i++ {
		nextOptedIn = append(nextOptedIn, providerAddresses[i])
	}

	var optedOut []types.ProviderConsAddress
	for i := 6; i < 10; i++ {
		optedOut = append(optedOut, providerAddresses[i])
	}

	expectedValUpdates := []abci.ValidatorUpdate{
		{PubKey: pubKeys[0], Power: 0},
		{PubKey: pubKeys[1], Power: 1},
		{PubKey: pubKeys[2], Power: 2},
		{PubKey: pubKeys[3], Power: 3},
		{PubKey: pubKeys[4], Power: 4},
		{PubKey: pubKeys[5], Power: 5},
		{PubKey: pubKeys[6], Power: 0},
		{PubKey: pubKeys[7], Power: 0},
		{PubKey: pubKeys[8], Power: 0},
		{PubKey: pubKeys[9], Power: 0},
	}

	actualValUpdates := providerKeeper.ComputePartialSetValidatorUpdates(ctx, nextOptedIn, optedOut)

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

func TestResetOptedInSet(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	// create 10 validators
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
		validator := stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
			Status:          stakingtypes.Bonded,
		}

		pubKey := tmprotocrypto.PublicKey{
			Sum: &tmprotocrypto.PublicKey_Ed25519{
				Ed25519: consAddr.Bytes(),
			},
		}
		pubKeys = append(pubKeys, pubKey)

		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(ctx, consAddr).Return(validator, true).AnyTimes()

		if i != 1 {
			mocks.MockStakingKeeper.EXPECT().
				GetLastValidatorPower(ctx, providerValidatorAddr).Return(int64(i + 1)).AnyTimes()
		} else {
			mocks.MockStakingKeeper.EXPECT().
				GetLastValidatorPower(ctx, providerValidatorAddr).Return(int64(0)).AnyTimes()
		}
	}

	// first 6 validators to opt in
	var toBeOptedIn []types.ProviderConsAddress

	providerKeeper.SetOptedIn(ctx, chainID, providerAddresses[0], 1, uint64(1))

	// this validator won't be added because it has a power of 0 .. .see above mock .. not here
	providerKeeper.SetOptedIn(ctx, chainID, providerAddresses[1], 1, uint64(3))

	for i := 2; i < 6; i++ {
		providerKeeper.SetToBeOptedIn(ctx, chainID, providerAddresses[i])
		toBeOptedIn = append(toBeOptedIn, providerAddresses[i])
	}

	var optedOut []types.ProviderConsAddress
	for i := 6; i < 10; i++ {
		providerKeeper.SetToBeOptedOut(ctx, chainID, providerAddresses[i])
		optedOut = append(optedOut, providerAddresses[i])
	}

	require.NotEmpty(t, providerKeeper.GetToBeOptedIn(ctx, chainID))
	require.NotEmpty(t, providerKeeper.GetToBeOptedOut(ctx, chainID))

	providerKeeper.ResetOptedInSet(ctx, chainID)

	require.Empty(t, providerKeeper.GetToBeOptedIn(ctx, chainID))
	require.Empty(t, providerKeeper.GetToBeOptedOut(ctx, chainID))

	actualOptedInValidators := providerKeeper.GetOptedIn(ctx, chainID)
	expectedOptedInValidators := []keeper.OptedInValidator{
		{ProviderAddr: providerAddresses[0], BlockHeight: 1, Power: 1},
		{ProviderAddr: providerAddresses[2], BlockHeight: uint64(ctx.BlockHeight()), Power: 3},
		{ProviderAddr: providerAddresses[3], BlockHeight: uint64(ctx.BlockHeight()), Power: 4},
		{ProviderAddr: providerAddresses[4], BlockHeight: uint64(ctx.BlockHeight()), Power: 5},
		{ProviderAddr: providerAddresses[5], BlockHeight: uint64(ctx.BlockHeight()), Power: 6},
	}

	sort.Slice(expectedOptedInValidators, func(i int, j int) bool {
		return strings.Compare(expectedOptedInValidators[i].ProviderAddr.String(), expectedOptedInValidators[j].ProviderAddr.String()) < 0
	})

	sort.Slice(actualOptedInValidators, func(i int, j int) bool {
		return strings.Compare(actualOptedInValidators[i].ProviderAddr.String(), actualOptedInValidators[j].ProviderAddr.String()) < 0
	})
	require.Equal(t, expectedOptedInValidators, actualOptedInValidators)
}
