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

	testkeeper "github.com/cosmos/interchain-security/v7/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

func TestHandleOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := providertypes.NewProviderConsAddress([]byte("providerAddr"))

	// trying to opt in to an unknown chain
	require.Error(t, providerKeeper.HandleOptIn(ctx, "unknownConsumerId", providerAddr, ""))

	// trying to opt in to a stopped consumer chain
	providerKeeper.SetConsumerPhase(ctx, "stoppedConsumerId", providertypes.CONSUMER_PHASE_STOPPED)
	require.Error(t, providerKeeper.HandleOptIn(ctx, "stoppedConsumerId", providerAddr, ""))

	providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_INITIALIZED)
	providerKeeper.SetConsumerChainId(ctx, CONSUMER_ID, "chainId")
	require.False(t, providerKeeper.IsOptedIn(ctx, CONSUMER_ID, providerAddr))
	err := providerKeeper.HandleOptIn(ctx, CONSUMER_ID, providerAddr, "")
	require.NoError(t, err)
	require.True(t, providerKeeper.IsOptedIn(ctx, CONSUMER_ID, providerAddr))
}

func TestHandleOptInWithConsumerKey(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// generate a consensus public key for the provider
	providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{1}).PubKey()
	consAddr := sdk.ConsAddress(providerConsPubKey.Address())
	providerAddr := providertypes.NewProviderConsAddress(consAddr)

	calls := []*gomock.Call{
		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(gomock.Any(), gomock.Any()).
			DoAndReturn(func(ctx sdk.Context, addr sdk.ConsAddress) (stakingtypes.Validator, error) {
				if addr.Equals(providerAddr.Address) {
					// Given `providerAddr`, `GetValidatorByConsAddr` returns a validator with the
					// exact same `ConsensusPubkey`
					pkAny, _ := codectypes.NewAnyWithValue(providerConsPubKey)
					return stakingtypes.Validator{ConsensusPubkey: pkAny}, nil
				} else {
					// for any other consensus address, we cannot find a validator
					return stakingtypes.Validator{}, stakingtypes.ErrNoValidatorFound
				}
			}).Times(2),
	}

	gomock.InOrder(calls...)

	// create a sample consumer key to assign to the `providerAddr` validator
	// on the consumer chain with `consumerId`
	consumerKey := "{\"@type\":\"/cosmos.crypto.ed25519.PubKey\",\"key\":\"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is=\"}"
	expectedConsumerPubKey, err := providerKeeper.ParseConsumerKey(consumerKey)
	require.NoError(t, err)

	providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_INITIALIZED)
	providerKeeper.SetConsumerChainId(ctx, CONSUMER_ID, CONSUMER_CHAIN_ID)
	err = providerKeeper.HandleOptIn(ctx, CONSUMER_ID, providerAddr, consumerKey)
	require.NoError(t, err)

	// assert that the consumeKey was assigned to `providerAddr` validator on chain with `consumerId`
	actualConsumerPubKey, found := providerKeeper.GetValidatorConsumerPubKey(ctx, CONSUMER_ID, providerAddr)
	require.True(t, found)
	require.Equal(t, expectedConsumerPubKey, actualConsumerPubKey)

	// assert that the `consumerAddr` to `providerAddr` association was set as well
	consumerAddr, _ := ccvtypes.TMCryptoPublicKeyToConsAddr(actualConsumerPubKey)
	actualProviderConsAddr, found := providerKeeper.GetValidatorByConsumerAddr(ctx, CONSUMER_ID, providertypes.NewConsumerConsAddress(consumerAddr))
	require.True(t, found)
	require.Equal(t, providerAddr, actualProviderConsAddr)
}

func TestHandleOptOut(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := CONSUMER_ID

	providerAddr := providertypes.NewProviderConsAddress([]byte("providerAddr"))

	// trying to opt out from a not running chain returns an error
	require.Error(t, providerKeeper.HandleOptOut(ctx, "unknownChainID", providerAddr))

	// set the phase and power shaping params
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)
	err := providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{})
	require.NoError(t, err)

	// if validator (`providerAddr`) is already opted in, then an opt-out would remove this validator
	providerKeeper.SetOptedIn(ctx, consumerId, providerAddr)
	require.True(t, providerKeeper.IsOptedIn(ctx, consumerId, providerAddr))
	err = providerKeeper.HandleOptOut(ctx, consumerId, providerAddr)
	require.NoError(t, err)
	require.False(t, providerKeeper.IsOptedIn(ctx, consumerId, providerAddr))
}

func TestHandleOptOutFromTopNChain(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := CONSUMER_ID

	// set the phase
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)

	// set the chain as Top 50 and create 4 validators with 10%, 20%, 30%, and 40% of the total voting power
	// respectively
	err := providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 50,
	})
	require.NoError(t, err)
	valA := createStakingValidator(ctx, mocks, 1, 1) // 10% of the total voting power (can opt out)
	valAConsAddr, _ := valA.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valAConsAddr).Return(valA, nil).AnyTimes()
	valB := createStakingValidator(ctx, mocks, 2, 2) // 20% of the total voting power (can opt out)
	valBConsAddr, _ := valB.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valBConsAddr).Return(valB, nil).AnyTimes()
	valC := createStakingValidator(ctx, mocks, 3, 3) // 30% of the total voting power (cannot opt out)
	valCConsAddr, _ := valC.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valCConsAddr).Return(valC, nil).AnyTimes()
	valD := createStakingValidator(ctx, mocks, 4, 4) // 40% of the total voting power (cannot opt out)
	valDConsAddr, _ := valD.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valDConsAddr).Return(valD, nil).AnyTimes()

	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 4, []stakingtypes.Validator{valA, valB, valC, valD}, -1) // -1 to allow mocks AnyTimes

	// initialize the minPowerInTopN correctly
	minPowerInTopN, err := providerKeeper.ComputeMinPowerInTopN(ctx, []stakingtypes.Validator{valA, valB, valC, valD}, 50)
	require.NoError(t, err)
	providerKeeper.SetMinimumPowerInTopN(ctx, consumerId, minPowerInTopN)

	// opt in all validators
	providerKeeper.SetOptedIn(ctx, consumerId, providertypes.NewProviderConsAddress(valAConsAddr))
	providerKeeper.SetOptedIn(ctx, consumerId, providertypes.NewProviderConsAddress(valBConsAddr))
	providerKeeper.SetOptedIn(ctx, consumerId, providertypes.NewProviderConsAddress(valCConsAddr))
	providerKeeper.SetOptedIn(ctx, consumerId, providertypes.NewProviderConsAddress(valDConsAddr))

	// validators A and B can opt out because they belong the bottom 30% of validators
	require.NoError(t, providerKeeper.HandleOptOut(ctx, consumerId, providertypes.NewProviderConsAddress(valAConsAddr)))
	require.NoError(t, providerKeeper.HandleOptOut(ctx, consumerId, providertypes.NewProviderConsAddress(valBConsAddr)))

	// validators C and D cannot opt out because C has 30% of the voting power and D has 40% of the voting power
	// and hence both are needed to keep validating a Top 50 chain
	require.Error(t, providerKeeper.HandleOptOut(ctx, consumerId, providertypes.NewProviderConsAddress(valCConsAddr)))
	require.Error(t, providerKeeper.HandleOptOut(ctx, consumerId, providertypes.NewProviderConsAddress(valDConsAddr)))

	// opting out a validator that cannot be found from a Top N chain should also return an error
	notFoundValidator := createStakingValidator(ctx, mocks, 5, 5)
	notFoundValidatorConsAddr, err := notFoundValidator.GetConsAddr()
	require.NoError(t, err)
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, notFoundValidatorConsAddr).
		Return(stakingtypes.Validator{}, stakingtypes.ErrNoValidatorFound)
	require.Error(t, providerKeeper.HandleOptOut(ctx, consumerId, providertypes.NewProviderConsAddress(notFoundValidatorConsAddr)))
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
	valD := createStakingValidator(ctx, mocks, 1, 4)
	valDConsAddr, _ := valD.GetConsAddr()

	// Start Test 1: opt in all validators with power >= 0
	err := providerKeeper.OptInTopNValidators(ctx, CONSUMER_ID, []stakingtypes.Validator{valA, valB, valC, valD}, 0)
	require.NoError(t, err)
	expectedOptedInValidators := []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress(valAConsAddr),
		providertypes.NewProviderConsAddress(valBConsAddr),
		providertypes.NewProviderConsAddress(valCConsAddr),
		providertypes.NewProviderConsAddress(valDConsAddr),
	}
	actualOptedInValidators := providerKeeper.GetAllOptedIn(ctx, CONSUMER_ID)

	// sort validators first to be able to compare
	sortUpdates := func(addresses []providertypes.ProviderConsAddress) {
		sort.Slice(addresses, func(i, j int) bool {
			return bytes.Compare(addresses[i].ToSdkConsAddr(), addresses[j].ToSdkConsAddr()) < 0
		})
	}

	sortUpdates(expectedOptedInValidators)
	sortUpdates(actualOptedInValidators)
	require.Equal(t, expectedOptedInValidators, actualOptedInValidators)

	// reset state for the upcoming checks
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valAConsAddr))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valBConsAddr))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valCConsAddr))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valDConsAddr))

	// Start Test 2: opt in all validators with power >= 1
	// We expect the same `expectedOptedInValidators` as when we opted in all validators with power >= 0 because the
	// validators with the smallest power have power == 1
	err = providerKeeper.OptInTopNValidators(ctx, CONSUMER_ID, []stakingtypes.Validator{valA, valB, valC, valD}, 0)
	require.NoError(t, err)
	actualOptedInValidators = providerKeeper.GetAllOptedIn(ctx, CONSUMER_ID)
	sortUpdates(actualOptedInValidators)
	require.Equal(t, expectedOptedInValidators, actualOptedInValidators)

	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valAConsAddr))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valBConsAddr))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valCConsAddr))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valDConsAddr))

	// Start Test 3: opt in all validators with power >= 2 and hence we do not expect to opt in validator A
	err = providerKeeper.OptInTopNValidators(ctx, CONSUMER_ID, []stakingtypes.Validator{valA, valB, valC, valD}, 2)
	require.NoError(t, err)
	expectedOptedInValidators = []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress(valBConsAddr),
		providertypes.NewProviderConsAddress(valCConsAddr),
	}
	actualOptedInValidators = providerKeeper.GetAllOptedIn(ctx, CONSUMER_ID)

	// sort validators first to be able to compare
	sortUpdates(expectedOptedInValidators)
	sortUpdates(actualOptedInValidators)
	require.Equal(t, expectedOptedInValidators, actualOptedInValidators)

	// reset state for the upcoming checks
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valAConsAddr))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valBConsAddr))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valCConsAddr))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, providertypes.NewProviderConsAddress(valDConsAddr))

	// Start Test 4: opt in all validators with power >= 4 and hence we do not expect any opted-in validators
	err = providerKeeper.OptInTopNValidators(ctx, CONSUMER_ID, []stakingtypes.Validator{valA, valB, valC, valD}, 4)
	require.NoError(t, err)
	require.Empty(t, providerKeeper.GetAllOptedIn(ctx, CONSUMER_ID))
}

func TestGetAllOptedIn(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	expectedOptedInValidators := []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress([]byte("providerAddr1")),
		providertypes.NewProviderConsAddress([]byte("providerAddr2")),
		providertypes.NewProviderConsAddress([]byte("providerAddr3")),
	}

	for _, expectedOptedInValidator := range expectedOptedInValidators {
		providerKeeper.SetOptedIn(ctx, CONSUMER_ID, expectedOptedInValidator)
	}

	actualOptedInValidators := providerKeeper.GetAllOptedIn(ctx, CONSUMER_ID)

	// sort validators first to be able to compare
	sortOptedInValidators := func(addresses []providertypes.ProviderConsAddress) {
		sort.Slice(addresses, func(i, j int) bool {
			return bytes.Compare(addresses[i].ToSdkConsAddr(), addresses[j].ToSdkConsAddr()) < 0
		})
	}
	sortOptedInValidators(expectedOptedInValidators)
	sortOptedInValidators(actualOptedInValidators)
	require.Equal(t, expectedOptedInValidators, actualOptedInValidators)
}

// TestOptedIn tests the `SetOptedIn`, `IsOptedIn`, `DeleteOptedIn` and `DeleteAllOptedIn` methods
func TestOptedIn(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	optedInValidator1 := providertypes.NewProviderConsAddress([]byte("providerAddr1"))
	optedInValidator2 := providertypes.NewProviderConsAddress([]byte("providerAddr2"))

	require.False(t, providerKeeper.IsOptedIn(ctx, CONSUMER_ID, optedInValidator1))
	providerKeeper.SetOptedIn(ctx, CONSUMER_ID, optedInValidator1)
	require.True(t, providerKeeper.IsOptedIn(ctx, CONSUMER_ID, optedInValidator1))
	providerKeeper.DeleteOptedIn(ctx, CONSUMER_ID, optedInValidator1)
	require.False(t, providerKeeper.IsOptedIn(ctx, CONSUMER_ID, optedInValidator1))

	providerKeeper.SetOptedIn(ctx, CONSUMER_ID, optedInValidator1)
	providerKeeper.SetOptedIn(ctx, CONSUMER_ID, optedInValidator2)
	require.True(t, providerKeeper.IsOptedIn(ctx, CONSUMER_ID, optedInValidator1))
	require.True(t, providerKeeper.IsOptedIn(ctx, CONSUMER_ID, optedInValidator2))
	providerKeeper.DeleteAllOptedIn(ctx, CONSUMER_ID)
	require.False(t, providerKeeper.IsOptedIn(ctx, CONSUMER_ID, optedInValidator1))
	require.False(t, providerKeeper.IsOptedIn(ctx, CONSUMER_ID, optedInValidator2))
}
