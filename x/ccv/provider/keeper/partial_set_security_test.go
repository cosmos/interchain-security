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
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	"sort"
	"testing"
)

func TestHandleOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

	// mock `GetValidatorByConsAddr` that returns a `Bonded` validator for the `providerAddr` address and
	// an `Unbonding` validator for any  other address
	mocks.MockStakingKeeper.EXPECT().
		GetValidatorByConsAddr(gomock.Any(), gomock.Any()).
		DoAndReturn(func(ctx sdk.Context, addr sdk.ConsAddress) (stakingtypes.Validator, bool) {
			if addr.Equals(providerAddr.Address) {
				pkAny, _ := codectypes.NewAnyWithValue(ed25519.GenPrivKeyFromSecret([]byte{1}).PubKey())
				return stakingtypes.Validator{ConsensusPubkey: pkAny, Status: stakingtypes.Bonded}, true
			} else {
				pkAny, _ := codectypes.NewAnyWithValue(ed25519.GenPrivKeyFromSecret([]byte{2}).PubKey())
				return stakingtypes.Validator{ConsensusPubkey: pkAny, Status: stakingtypes.Unbonding}, true
			}
		}).AnyTimes()

	// verify that a non-`Bonded` validator cannot opt in
	unbondedProviderAddr := types.NewProviderConsAddress([]byte("unbondedProviderAddr"))
	providerKeeper.SetProposedConsumerChain(ctx, "someChainID", 1)
	require.Error(t, providerKeeper.HandleOptIn(ctx, "someChainID", unbondedProviderAddr, nil))

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
	providerKeeper.SetOptedIn(ctx, "chainID", providerAddr, 1)
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
			}).Times(3),
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

func TestGetToBeOptedInValidatorUpdates(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	type TestValidator struct {
		validator         stakingtypes.Validator
		power             int64
		expectedValUpdate abci.ValidatorUpdate
	}

	chainID := "chainID"

	var testValidators []TestValidator
	for i := int64(0); i < 10; i++ {
		// generate a consensus public key for the provider
		providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{uint8(i)}).PubKey()
		consAddr := sdk.ConsAddress(providerConsPubKey.Address())
		providerAddr := types.NewProviderConsAddress(consAddr)

		foo := providerAddr.Address.Bytes()
		var providerValidatorAddr sdk.ValAddress
		providerValidatorAddr = foo

		var status stakingtypes.BondStatus
		if i%3 == 0 {
			status = stakingtypes.Unbonded
		} else if i%3 == 1 {
			status = stakingtypes.Bonded
		} else {
			status = stakingtypes.Unbonding
		}

		pkAny, _ := codectypes.NewAnyWithValue(providerConsPubKey)
		validator := stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
			Status:          status,
		}

		consumerTMPublicKey := tmprotocrypto.PublicKey{
			Sum: &tmprotocrypto.PublicKey_Ed25519{
				Ed25519: consAddr.Bytes(),
			},
		}

		expectedValUpdate := abci.ValidatorUpdate{PubKey: consumerTMPublicKey, Power: i}

		testValidators = append(testValidators,
			TestValidator{validator: validator, power: i, expectedValUpdate: expectedValUpdate})

		providerKeeper.SetToBeOptedIn(ctx, chainID, providerAddr)
	}

	for _, val := range testValidators {
		consAddr, _ := val.validator.GetConsAddr()
		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(ctx, consAddr).Return(val.validator, true).AnyTimes()
		mocks.MockStakingKeeper.EXPECT().
			GetLastValidatorPower(ctx, val.validator.GetOperator()).Return(val.power).AnyTimes()
	}

	var expectedValUpdates []abci.ValidatorUpdate
	for _, val := range testValidators {
		if !val.validator.IsBonded() {
			continue
		}
		expectedValUpdates = append(expectedValUpdates, val.expectedValUpdate)
	}

	actualValUpdates := providerKeeper.GetToBeOptedInValidatorUpdates(ctx, chainID)

	// sort before comparing
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

func TestGetToBeOptedOutValidatorUpdates(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	type TestValidator struct {
		validator         stakingtypes.Validator
		power             int64
		expectedValUpdate abci.ValidatorUpdate
	}

	chainID := "chainID"

	var testValidators []TestValidator
	for i := int64(0); i < 10; i++ {
		// generate a consensus public key for the provider
		providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{uint8(i)}).PubKey()
		consAddr := sdk.ConsAddress(providerConsPubKey.Address())
		providerAddr := types.NewProviderConsAddress(consAddr)

		foo := providerAddr.Address.Bytes()
		var providerValidatorAddr sdk.ValAddress
		providerValidatorAddr = foo

		pkAny, _ := codectypes.NewAnyWithValue(providerConsPubKey)
		validator := stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
		}

		consumerTMPublicKey := tmprotocrypto.PublicKey{
			Sum: &tmprotocrypto.PublicKey_Ed25519{
				Ed25519: consAddr.Bytes(),
			},
		}

		expectedValUpdate := abci.ValidatorUpdate{PubKey: consumerTMPublicKey, Power: 0}

		testValidators = append(testValidators,
			TestValidator{validator: validator, power: i, expectedValUpdate: expectedValUpdate})

		providerKeeper.SetToBeOptedOut(ctx, chainID, providerAddr)
	}

	for _, val := range testValidators {
		consAddr, _ := val.validator.GetConsAddr()
		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(ctx, consAddr).Return(val.validator, true).AnyTimes()
	}

	var expectedValUpdates []abci.ValidatorUpdate
	for _, val := range testValidators {
		expectedValUpdates = append(expectedValUpdates, val.expectedValUpdate)
	}

	actualValUpdates := providerKeeper.GetToBeOptedOutValidatorUpdates(ctx, chainID)

	// sort before comparing
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

func createValidators(bondStatutes []stakingtypes.BondStatus, powers []int64) (validators []stakingtypes.Validator,
	valUpdates []abci.ValidatorUpdate) {
	if len(bondStatutes) != len(powers) {
		return
	}

	for i := 0; i < len(bondStatutes); i++ {
		providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{uint8(i)}).PubKey()
		consAddr := sdk.ConsAddress(providerConsPubKey.Address())
		providerAddr := types.NewProviderConsAddress(consAddr)

		var providerValidatorAddr sdk.ValAddress
		providerValidatorAddr = providerAddr.Address.Bytes()

		pkAny, _ := codectypes.NewAnyWithValue(providerConsPubKey)
		validator := stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
			Status:          bondStatutes[i],
		}
		validators = append(validators, validator)

		consumerTMPublicKey := tmprotocrypto.PublicKey{
			Sum: &tmprotocrypto.PublicKey_Ed25519{
				Ed25519: consAddr.Bytes(),
			},
		}

		valUpdate := abci.ValidatorUpdate{PubKey: consumerTMPublicKey, Power: powers[i]}
		valUpdates = append(valUpdates, valUpdate)
	}
	return
}

func TestComputePartialValidatorUpdateSet(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	type TestValidator struct {
		validator         stakingtypes.Validator
		power             int64
		expectedValUpdate abci.ValidatorUpdate
	}

	chainID := "chainID"

	// create 10 validator updates
	//var updates []abci.ValidatorUpdate
	powers := []int64{1, 2, 3, 4, 5, 6}
	vals, updates := createValidators(
		[]stakingtypes.BondStatus{stakingtypes.Bonded, stakingtypes.Unbonding, stakingtypes.Bonded, stakingtypes.Unbonded,
			stakingtypes.Unbonded, stakingtypes.Bonded}, powers)

	addr0, _ := vals[0].GetConsAddr()
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(addr0), uint64(1))
	addr1, _ := vals[1].GetConsAddr()
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(addr1), uint64(2))
	addr2, _ := vals[2].GetConsAddr()
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(addr2), uint64(3))
	addr3, _ := vals[3].GetConsAddr()
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(addr3), uint64(4))

	// set to be opted out
	providerKeeper.SetToBeOptedOut(ctx, chainID, types.NewProviderConsAddress(addr2))
	providerKeeper.SetToBeOptedOut(ctx, chainID, types.NewProviderConsAddress(addr3))

	// make all the validators at once ...  kane to stakingUpdates based on the publickeys of those validators and then get the result
	addr4, _ := vals[4].GetConsAddr()
	providerKeeper.SetToBeOptedIn(ctx, chainID, types.NewProviderConsAddress(addr4))
	addr5, _ := vals[5].GetConsAddr()
	providerKeeper.SetToBeOptedIn(ctx, chainID, types.NewProviderConsAddress(addr5))

	for i, val := range vals {
		consAddr, _ := val.GetConsAddr()
		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(ctx, consAddr).Return(val, true).AnyTimes()
		mocks.MockStakingKeeper.EXPECT().
			GetLastValidatorPower(ctx, val.GetOperator()).Return(powers[i]).AnyTimes()
	}

	actualValUpdates := providerKeeper.ComputePartialSetValUpdates(ctx, chainID, []abci.ValidatorUpdate{})

	fmt.Println(updates)
	fmt.Println(actualValUpdates)
	//require.Equal(t, expectedValUpdates, actualValUpdates)
}

func TestResetPartialSet(t *testing.T) {
	// s
}
