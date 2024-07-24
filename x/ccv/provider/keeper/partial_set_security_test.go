package keeper_test

import (
	"bytes"
	"sort"
	"testing"

	gomath "math"

	"cosmossdk.io/math"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	"pgregory.net/rapid"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cometbft/cometbft/proto/tendermint/crypto"

	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

func TestHandleOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

	// trying to opt in to a non-proposed and non-registered chain returns an error
	require.Error(t, providerKeeper.HandleOptIn(ctx, "unknownChainID", providerAddr, ""))

	providerKeeper.SetProposedConsumerChain(ctx, "chainID", 1)
	require.False(t, providerKeeper.IsOptedIn(ctx, "chainID", providerAddr))
	providerKeeper.HandleOptIn(ctx, "chainID", providerAddr, "")
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
	providerKeeper.SetProposedConsumerChain(ctx, "chainID", 1)

	// create a sample consumer key to assign to the `providerAddr` validator
	// on the consumer chain with id `chainID`
	consumerKey := "{\"@type\":\"/cosmos.crypto.ed25519.PubKey\",\"key\":\"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is=\"}"
	expectedConsumerPubKey, err := providerKeeper.ParseConsumerKey(consumerKey)
	require.NoError(t, err)

	err = providerKeeper.HandleOptIn(ctx, "chainID", providerAddr, consumerKey)
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

func TestHandleOptOutFromTopNChain(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	// set a consumer client so that the chain is considered running
	providerKeeper.SetConsumerClientId(ctx, chainID, "clientID")

	// set the chain as Top 50 and create 4 validators with 10%, 20%, 30%, and 40% of the total voting power
	// respectively
	providerKeeper.SetTopN(ctx, "chainID", 50)
	valA := createStakingValidator(ctx, mocks, 1, 1, 1) // 10% of the total voting power (can opt out)
	valAConsAddr, _ := valA.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valAConsAddr).Return(valA, nil).AnyTimes()
	valB := createStakingValidator(ctx, mocks, 2, 2, 2) // 20% of the total voting power (can opt out)
	valBConsAddr, _ := valB.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valBConsAddr).Return(valB, nil).AnyTimes()
	valC := createStakingValidator(ctx, mocks, 3, 3, 3) // 30% of the total voting power (cannot opt out)
	valCConsAddr, _ := valC.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valCConsAddr).Return(valC, nil).AnyTimes()
	valD := createStakingValidator(ctx, mocks, 4, 4, 4) // 40% of the total voting power (cannot opt out)
	valDConsAddr, _ := valD.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valDConsAddr).Return(valD, nil).AnyTimes()

	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 4, []stakingtypes.Validator{valA, valB, valC, valD}, []int64{1, 2, 3, 4}, -1) // -1 to allow mocks AnyTimes

	// initialize the minPowerInTopN correctly
	minPowerInTopN, err := providerKeeper.ComputeMinPowerInTopN(ctx, []stakingtypes.Validator{valA, valB, valC, valD}, 50)
	require.NoError(t, err)
	providerKeeper.SetMinimumPowerInTopN(ctx, chainID, minPowerInTopN)

	// opt in all validators
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(valAConsAddr))
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(valBConsAddr))
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(valCConsAddr))
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(valDConsAddr))

	// validators A and B can opt out because they belong the bottom 30% of validators
	require.NoError(t, providerKeeper.HandleOptOut(ctx, chainID, types.NewProviderConsAddress(valAConsAddr)))
	require.NoError(t, providerKeeper.HandleOptOut(ctx, chainID, types.NewProviderConsAddress(valBConsAddr)))

	// validators C and D cannot opt out because C has 30% of the voting power and D has 40% of the voting power
	// and hence both are needed to keep validating a Top 50 chain
	require.Error(t, providerKeeper.HandleOptOut(ctx, chainID, types.NewProviderConsAddress(valCConsAddr)))
	require.Error(t, providerKeeper.HandleOptOut(ctx, chainID, types.NewProviderConsAddress(valDConsAddr)))

	// opting out a validator that cannot be found from a Top N chain should also return an error
	notFoundValidator := createStakingValidator(ctx, mocks, 5, 5, 5)
	notFoundValidatorConsAddr, _ := notFoundValidator.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, notFoundValidatorConsAddr).
		Return(stakingtypes.Validator{}, stakingtypes.ErrNoValidatorFound)
	require.Error(t, providerKeeper.HandleOptOut(ctx, chainID, types.NewProviderConsAddress(notFoundValidatorConsAddr)))
}

func TestHandleSetConsumerCommissionRate(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

	// trying to set a commission rate to a unknown consumer chain
	require.Error(t, providerKeeper.HandleSetConsumerCommissionRate(ctx, "unknownChainID", providerAddr, math.LegacyZeroDec()))

	// setup a pending consumer chain
	chainID := "pendingChainID"
	providerKeeper.SetPendingConsumerAdditionProp(ctx, &types.ConsumerAdditionProposal{ChainId: chainID})

	// check that there's no commission rate set for the validator yet
	_, found := providerKeeper.GetConsumerCommissionRate(ctx, chainID, providerAddr)
	require.False(t, found)

	mocks.MockStakingKeeper.EXPECT().MinCommissionRate(ctx).Return(math.LegacyZeroDec(), nil).Times(1)
	require.NoError(t, providerKeeper.HandleSetConsumerCommissionRate(ctx, chainID, providerAddr, math.LegacyOneDec()))

	// check that the commission rate is now set
	cr, found := providerKeeper.GetConsumerCommissionRate(ctx, chainID, providerAddr)
	require.Equal(t, math.LegacyOneDec(), cr)
	require.True(t, found)

	// set minimum rate of 1/2
	commissionRate := math.LegacyNewDec(1).Quo(math.LegacyNewDec(2))
	mocks.MockStakingKeeper.EXPECT().MinCommissionRate(ctx).Return(commissionRate, nil).AnyTimes()

	// try to set a rate slightly below the minimum
	require.Error(t, providerKeeper.HandleSetConsumerCommissionRate(
		ctx,
		chainID,
		providerAddr,
		commissionRate.Sub(math.LegacyNewDec(1).Quo(math.LegacyNewDec(100)))), // 0.5 - 0.01
		"commission rate should be rejected (below min), but is not",
	)

	// set a valid commission equal to the minimum
	require.NoError(t, providerKeeper.HandleSetConsumerCommissionRate(ctx, chainID, providerAddr, commissionRate))
	// check that the rate was set
	cr, found = providerKeeper.GetConsumerCommissionRate(ctx, chainID, providerAddr)
	require.Equal(t, commissionRate, cr)
	require.True(t, found)
}

func TestOptInTopNValidators(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create 4 validators with powers 1, 2, 3, and 1 respectively
	valA := createStakingValidator(ctx, mocks, 1, 1, 1)
	valAConsAddr, _ := valA.GetConsAddr()
	valB := createStakingValidator(ctx, mocks, 2, 2, 2)
	valBConsAddr, _ := valB.GetConsAddr()
	valC := createStakingValidator(ctx, mocks, 3, 3, 3)
	valCConsAddr, _ := valC.GetConsAddr()
	valD := createStakingValidator(ctx, mocks, 4, 1, 4)
	valDConsAddr, _ := valD.GetConsAddr()

	// Start Test 1: opt in all validators with power >= 0
	providerKeeper.OptInTopNValidators(ctx, "chainID", []stakingtypes.Validator{valA, valB, valC, valD}, 0)
	expectedOptedInValidators := []types.ProviderConsAddress{
		types.NewProviderConsAddress(valAConsAddr),
		types.NewProviderConsAddress(valBConsAddr),
		types.NewProviderConsAddress(valCConsAddr),
		types.NewProviderConsAddress(valDConsAddr),
	}
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
		types.NewProviderConsAddress(valCConsAddr),
	}
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

func TestComputeMinPowerInTopN(t *testing.T) {
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
		createStakingValidator(ctx, mocks, 1, 5, 1),
		createStakingValidator(ctx, mocks, 2, 10, 2),
		createStakingValidator(ctx, mocks, 3, 3, 3),
		createStakingValidator(ctx, mocks, 4, 1, 4),
		createStakingValidator(ctx, mocks, 5, 6, 5),
	}

	m, err := providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 100)
	require.NoError(t, err)
	require.Equal(t, int64(1), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 97)
	require.NoError(t, err)
	require.Equal(t, int64(1), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 96)
	require.NoError(t, err)
	require.Equal(t, int64(3), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 85)
	require.NoError(t, err)
	require.Equal(t, int64(3), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 84)
	require.NoError(t, err)
	require.Equal(t, int64(5), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 65)
	require.NoError(t, err)
	require.Equal(t, int64(5), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 64)
	require.NoError(t, err)
	require.Equal(t, int64(6), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 50)
	require.NoError(t, err)
	require.Equal(t, int64(6), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 40)
	require.NoError(t, err)
	require.Equal(t, int64(10), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 1)
	require.NoError(t, err)
	require.Equal(t, int64(10), m)

	_, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 0)
	require.Error(t, err)

	_, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 101)
	require.Error(t, err)
}

// TestCanValidateChain returns true if `validator` is opted in, in `chainID.
func TestCanValidateChain(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator := createStakingValidator(ctx, mocks, 0, 1, 1)
	consAddr, _ := validator.GetConsAddr()
	providerAddr := types.NewProviderConsAddress(consAddr)

	// with no allowlist or denylist, the validator has to be opted in, in order to consider it
	require.False(t, providerKeeper.CanValidateChain(ctx, "chainID", providerAddr))
	providerKeeper.SetOptedIn(ctx, "chainID", types.NewProviderConsAddress(consAddr))
	require.True(t, providerKeeper.CanValidateChain(ctx, "chainID", providerAddr))

	// create an allow list but do not add the validator `providerAddr` to it
	validatorA := createStakingValidator(ctx, mocks, 1, 1, 2)
	consAddrA, _ := validatorA.GetConsAddr()
	providerKeeper.SetAllowlist(ctx, "chainID", types.NewProviderConsAddress(consAddrA))
	require.False(t, providerKeeper.CanValidateChain(ctx, "chainID", providerAddr))
	providerKeeper.SetAllowlist(ctx, "chainID", types.NewProviderConsAddress(consAddr))
	require.True(t, providerKeeper.CanValidateChain(ctx, "chainID", providerAddr))

	// create a denylist but do not add validator `providerAddr` to it
	providerKeeper.SetDenylist(ctx, "chainID", types.NewProviderConsAddress(consAddrA))
	require.True(t, providerKeeper.CanValidateChain(ctx, "chainID", providerAddr))
	// add validator `providerAddr` to the denylist
	providerKeeper.SetDenylist(ctx, "chainID", types.NewProviderConsAddress(consAddr))
	require.False(t, providerKeeper.CanValidateChain(ctx, "chainID", providerAddr))
}

func TestCapValidatorSet(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validatorA := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrA"),
		Power:            1,
		PublicKey:        &crypto.PublicKey{},
	}

	validatorB := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrB"),
		Power:            2,
		PublicKey:        &crypto.PublicKey{},
	}

	validatorC := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrC"),
		Power:            3,
		PublicKey:        &crypto.PublicKey{},
	}
	validators := []types.ConsensusValidator{validatorA, validatorB, validatorC}

	consumerValidators := providerKeeper.CapValidatorSet(ctx, "chainID", validators)
	require.Equal(t, validators, consumerValidators)

	providerKeeper.SetValidatorSetCap(ctx, "chainID", 0)
	consumerValidators = providerKeeper.CapValidatorSet(ctx, "chainID", validators)
	require.Equal(t, validators, consumerValidators)

	providerKeeper.SetValidatorSetCap(ctx, "chainID", 100)
	consumerValidators = providerKeeper.CapValidatorSet(ctx, "chainID", validators)
	require.Equal(t, validators, consumerValidators)

	providerKeeper.SetValidatorSetCap(ctx, "chainID", 1)
	consumerValidators = providerKeeper.CapValidatorSet(ctx, "chainID", validators)
	require.Equal(t, []types.ConsensusValidator{validatorC}, consumerValidators)

	providerKeeper.SetValidatorSetCap(ctx, "chainID", 2)
	consumerValidators = providerKeeper.CapValidatorSet(ctx, "chainID", validators)
	require.Equal(t, []types.ConsensusValidator{validatorC, validatorB}, consumerValidators)

	providerKeeper.SetValidatorSetCap(ctx, "chainID", 3)
	consumerValidators = providerKeeper.CapValidatorSet(ctx, "chainID", validators)
	require.Equal(t, []types.ConsensusValidator{validatorC, validatorB, validatorA}, consumerValidators)
}

func TestCapValidatorsPower(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validatorA := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrA"),
		Power:            1,
		PublicKey:        &crypto.PublicKey{},
	}

	validatorB := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrB"),
		Power:            2,
		PublicKey:        &crypto.PublicKey{},
	}

	validatorC := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrC"),
		Power:            3,
		PublicKey:        &crypto.PublicKey{},
	}

	validatorD := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrD"),
		Power:            4,
		PublicKey:        &crypto.PublicKey{},
	}

	validators := []types.ConsensusValidator{validatorA, validatorB, validatorC, validatorD}

	expectedValidators := make([]types.ConsensusValidator, len(validators))
	copy(expectedValidators, validators)
	expectedValidators[0].Power = 2
	expectedValidators[1].Power = 2
	expectedValidators[2].Power = 3
	expectedValidators[3].Power = 3

	sortValidators := func(validators []types.ConsensusValidator) {
		sort.Slice(validators, func(i, j int) bool {
			return bytes.Compare(validators[i].ProviderConsAddr, validators[j].ProviderConsAddr) < 0
		})
	}

	// no capping takes place because validators power-cap is not set
	cappedValidators := providerKeeper.CapValidatorsPower(ctx, "chainID", validators)
	sortValidators(validators)
	sortValidators(cappedValidators)
	require.Equal(t, validators, cappedValidators)

	providerKeeper.SetValidatorsPowerCap(ctx, "chainID", 33)
	cappedValidators = providerKeeper.CapValidatorsPower(ctx, "chainID", validators)
	sortValidators(expectedValidators)
	sortValidators(cappedValidators)
	require.Equal(t, expectedValidators, cappedValidators)
}

func TestNoMoreThanPercentOfTheSum(t *testing.T) {
	// **impossible** case where we only have 9 powers, and we want that no number has more than 10% of the total sum
	powers := []int64{1, 2, 3, 4, 5, 6, 7, 8, 9}
	percent := uint32(10)
	require.False(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 20
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 21
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 25
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 32
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 33
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 34
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 50
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))
}

func createConsumerValidators(powers []int64) []types.ConsensusValidator {
	var validators []types.ConsensusValidator
	for _, p := range powers {
		validators = append(validators, types.ConsensusValidator{
			ProviderConsAddr: []byte("providerConsAddr"),
			Power:            p,
			PublicKey:        &crypto.PublicKey{},
		})
	}
	return validators
}

// returns `true` if no validator in `validators` corresponds to more than `percent` of the total sum of all
// validators' powers
func noMoreThanPercent(validators []types.ConsensusValidator, percent uint32) bool {
	sum := int64(0)
	for _, v := range validators {
		sum = sum + v.Power
	}

	for _, v := range validators {
		if float64(v.Power)*100.0 > float64(percent)*float64(sum) {
			return false
		}
	}
	return true
}

func sumPowers(vals []types.ConsensusValidator) int64 {
	sum := int64(0)
	for _, v := range vals {
		sum += v.Power
	}
	return sum
}

func CapSatisfiable(vals []types.ConsensusValidator, percent uint32) bool {
	// 100 / len(vals) is what each validator gets if each has the same power.
	// if this is more than the cap, it cannot be satisfied.
	return float64(100)/float64(len(vals)) < float64(percent)
}

func TestNoMoreThanPercentOfTheSumProps(t *testing.T) {
	// define properties to test

	// capRespectedIfSatisfiable: if the cap can be respected, then it will be respected
	capRespectedIfSatisfiable := func(valsBefore, valsAfter []types.ConsensusValidator, percent uint32) bool {
		if CapSatisfiable(valsBefore, percent) {
			return noMoreThanPercent(valsAfter, percent)
		}
		return true
	}

	evenPowersIfCapCannotBeSatisfied := func(valsBefore, valsAfter []types.ConsensusValidator, percent uint32) bool {
		if !CapSatisfiable(valsBefore, percent) {
			// if the cap cannot be satisfied, each validator should have the same power
			for _, valAfter := range valsAfter {
				if valAfter.Power != valsAfter[0].Power {
					return false
				}
			}
		}
		return true
	}

	// fairness: if before, v1 has more power than v2, then afterwards v1 will not have less power than v2
	// (they might get the same power if they are both capped)
	fairness := func(valsBefore, valsAfter []types.ConsensusValidator) bool {
		for i, v := range valsBefore {
			// find the validator after with the same address
			vAfter := findConsumerValidator(t, v, valsAfter)

			// go through all other validators before (after this one, to avoid double checking)
			for j := i + 1; j < len(valsBefore); j++ {
				otherV := valsBefore[j]
				otherVAfter := findConsumerValidator(t, otherV, valsAfter)

				// v has at least as much power before
				if v.Power >= otherV.Power {
					// then otherV should not have more power after
					if vAfter.Power < otherVAfter.Power {
						return false
					}
				} else {
					// v has less power before
					// then v should not have more power after
					if vAfter.Power > otherVAfter.Power {
						return false
					}
				}
			}
		}
		return true
	}

	// non-zero: v has non-zero power before IFF it has non-zero power after
	nonZero := func(valsBefore, valsAfter []types.ConsensusValidator) bool {
		for _, v := range valsBefore {
			vAfter := findConsumerValidator(t, v, valsAfter)
			if (v.Power == 0) != (vAfter.Power == 0) {
				return false
			}
		}
		return true
	}

	// equalSumIfCapSatisfiable: the sum of the powers of the validators will not change if the cap can be satisfied
	// (except for small changes by rounding errors)
	equalSumIfCapSatisfiable := func(valsBefore, valsAfter []types.ConsensusValidator, percent uint32) bool {
		if CapSatisfiable(valsBefore, percent) {
			difference := gomath.Abs(float64(sumPowers(valsBefore) - sumPowers(valsAfter)))
			if difference > 1 {
				// if the difference is more than a rounding error, they are not equal
				return false
			}
		}
		return true
	}

	// num validators: the number of validators will not change
	equalNumVals := func(valsBefore, valsAfter []types.ConsensusValidator) bool {
		return len(valsBefore) == len(valsAfter)
	}

	// test setup for pbt
	rapid.Check(t, func(t *rapid.T) {
		powers := rapid.SliceOf(rapid.Int64Range(1, 1000000000000)).Draw(t, "powers")
		percent := uint32(rapid.Int32Range(1, 100).Draw(t, "percent"))

		consumerValidators := createConsumerValidators(powers)
		cappedValidators := keeper.NoMoreThanPercentOfTheSum(consumerValidators, percent)

		t.Log("can the cap be satisfied: ", CapSatisfiable(consumerValidators, percent))
		t.Log("before: ", consumerValidators)
		t.Log("after: ", cappedValidators)

		// check properties
		require.True(t, capRespectedIfSatisfiable(consumerValidators, cappedValidators, percent))
		require.True(t, evenPowersIfCapCannotBeSatisfied(consumerValidators, cappedValidators, percent))
		require.True(t, fairness(consumerValidators, cappedValidators))
		require.True(t, nonZero(consumerValidators, cappedValidators))
		require.True(t, equalSumIfCapSatisfiable(consumerValidators, cappedValidators, percent), "sum before: %v, sum after: %v", sumPowers(consumerValidators), sumPowers(cappedValidators))
		require.True(t, equalNumVals(consumerValidators, cappedValidators), "num before: %v, num after: %v", len(consumerValidators), len(cappedValidators))
	})
}

func findConsumerValidator(t *testing.T, v types.ConsensusValidator, valsAfter []types.ConsensusValidator) *types.ConsensusValidator {
	var vAfter *types.ConsensusValidator
	for _, vA := range valsAfter {
		if bytes.Equal(v.ProviderConsAddr, vA.ProviderConsAddr) {
			vAfter = &vA
			break
		}
	}
	if vAfter == nil {
		t.Fatalf("could not find validator with address %v in validators after \n validators after capping: %v", v.ProviderConsAddr, valsAfter)
	}
	return vAfter
}

func createStakingValidatorsAndMocks(ctx sdk.Context, mocks testkeeper.MockedKeepers, powers ...int64) ([]stakingtypes.Validator, []types.ProviderConsAddress) {
	var validators []stakingtypes.Validator
	for i, power := range powers {
		val := createStakingValidator(ctx, mocks, i, power, i)
		val.Tokens = math.NewInt(power)
		val.Status = stakingtypes.Bonded
		validators = append(validators, val)
	}

	var consAddrs []types.ProviderConsAddress
	for _, val := range validators {
		consAddr, err := val.GetConsAddr()
		if err != nil {
			panic(err)
		}
		consAddrs = append(consAddrs, types.NewProviderConsAddress(consAddr))
	}
	// set up mocks
	for index, val := range validators {
		mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, consAddrs[index].Address).Return(val, nil).AnyTimes()
	}

	return validators, consAddrs
}

// TestMinStake checks that FulfillsMinStake returns true if the validator has more than the min stake
// and false otherwise
func TestMinStake(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create two validators with powers 1 and 2
	_, consAddrs := createStakingValidatorsAndMocks(ctx, mocks, 1, 2)

	testCases := []struct {
		name           string
		minStake       uint64
		expectedFulfil []bool
	}{
		{
			name:           "No min stake",
			minStake:       0,
			expectedFulfil: []bool{true, true},
		},
		{
			name:           "Min stake set to 2",
			minStake:       2,
			expectedFulfil: []bool{false, true},
		},
		{
			name:           "Min stake set to 3",
			minStake:       3,
			expectedFulfil: []bool{false, false},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			providerKeeper.SetMinStake(ctx, "chainID", tc.minStake)
			for i, valAddr := range consAddrs {
				result := providerKeeper.FulfillsMinStake(ctx, "chainID", valAddr)
				require.Equal(t, tc.expectedFulfil[i], result)
			}
		})
	}
}

func TestMaxValidatorRank(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create validators
	vals, consAddrs := createStakingValidatorsAndMocks(ctx, mocks, 1, 2, 3, 4, 5, 5)

	// opt the validators in
	for _, valAddr := range consAddrs {
		providerKeeper.SetOptedIn(ctx, "chainID", valAddr)
	}

	testCases := []struct {
		name                      string
		maxRank                   uint32
		expectedProviderConsAddrs []types.ProviderConsAddress
	}{
		{
			name:                      "No max rank",
			maxRank:                   0,
			expectedProviderConsAddrs: consAddrs,
		},
		{
			name:    "Max rank set to 1",
			maxRank: 1,
			// include the last two validators which each have 5 power
			expectedProviderConsAddrs: consAddrs[len(consAddrs)-2:],
		},
		{
			name:    "Max rank set to 2",
			maxRank: 2,
			// still only include the last two validators
			expectedProviderConsAddrs: consAddrs[len(consAddrs)-2:],
		},
		{
			name:    "Max rank set to 3",
			maxRank: 3,
			// now include the third to last validator as well
			expectedProviderConsAddrs: consAddrs[len(consAddrs)-3:],
		},
		{
			name:                      "Max rank set to 6",
			maxRank:                   6,
			expectedProviderConsAddrs: consAddrs,
		},
		{
			name:                      "Max rank set to 10",
			maxRank:                   10,
			expectedProviderConsAddrs: consAddrs,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			providerKeeper.SetMaxValidatorRank(ctx, "chainID", tc.maxRank)

			// set max provider consensus vals to include all validators
			params := providerKeeper.GetParams(ctx)
			params.MaxProviderConsensusValidators = 180
			providerKeeper.SetParams(ctx, params)

			nextVals := providerKeeper.ComputeNextValidators(ctx, "chainID", vals)
			nextConsAddrs := make([]types.ProviderConsAddress, len(nextVals))
			for i, val := range nextVals {
				nextConsAddrs[i] = types.NewProviderConsAddress(val.ProviderConsAddr)
			}
			// check that the expected validators are the same as the next validator set, disregarding ordering
			require.ElementsMatch(t, tc.expectedProviderConsAddrs, nextConsAddrs)
		})
	}
}

// TestMaxProviderConsensusValidators checks that the number of validators in the next validator set is at most
// the maxProviderConsensusValidators parameter if the consumer chain does not allow inactive validators to validate.
func TestIfInactiveValsDisallowedProperty(t *testing.T) {
	rapid.Check(t, func(r *rapid.T) {
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		// Generate a random number of validators with random powers
		valPowers := rapid.SliceOfN(rapid.Int64Range(1, 100), 1, 100).Draw(r, "valPowers")
		vals, consAddrs := createStakingValidatorsAndMocks(ctx, mocks, valPowers...)

		// opt the validators in
		for _, valAddr := range consAddrs {
			providerKeeper.SetOptedIn(ctx, "chainID", valAddr)
		}

		// Randomly choose values for parameters
		minStake := rapid.Uint64Range(0, 101).Draw(r, "minStake")
		maxRank := rapid.Uint32Range(0, 11).Draw(r, "maxRank")
		maxProviderConsensusVals := rapid.Uint32Range(1, 11).Draw(r, "maxProviderConsensusVals")

		// Set up the parameters in the provider keeper
		providerKeeper.SetAllowInactiveValidators(ctx, "chainID", false) // do not allow inactive validators
		providerKeeper.SetMinStake(ctx, "chainID", minStake)
		providerKeeper.SetMaxValidatorRank(ctx, "chainID", maxRank)
		params := providerKeeper.GetParams(ctx)
		params.MaxProviderConsensusValidators = int64(maxProviderConsensusVals)
		providerKeeper.SetParams(ctx, params)

		// Compute the next validators
		nextVals := providerKeeper.ComputeNextValidators(ctx, "chainID", vals)

		// Check that the length of nextVals is at most maxProviderConsensusVals
		require.LessOrEqual(r, len(nextVals), int(maxProviderConsensusVals), "The length of nextVals should be at most maxProviderConsensusVals")

		// Sanity check: we only get 0 next validators if either:
		// - maxProviderConsensusVals is 0
		// - the maximal validator power is less than the min stake
		if len(nextVals) == 0 {
			maxValPower := int64(0)
			for _, power := range valPowers {
				if power > maxValPower {
					maxValPower = power
				}
			}
			require.True(
				r,
				maxProviderConsensusVals == 0 || maxValPower < int64(minStake),
				"The length of nextVals should only be 0 if either maxProviderConsensusVals is 0 or the maximal validator power is less than the min stake",
			)
		}
	})
}
