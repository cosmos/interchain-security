package keeper_test

import (
	"bytes"
	"sort"
	"testing"

	"github.com/stretchr/testify/require"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/proto/tendermint/crypto"

	cryptotestutil "github.com/cosmos/interchain-security/v7/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v7/testutil/keeper"
	"github.com/cosmos/interchain-security/v7/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
)

// TestConsumerValidator tests the `SetConsumerValidator`, `IsConsumerValidator`, and `DeleteConsumerValidator` methods
func TestConsumerValidator(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddr"),
		Power:            2,
		PublicKey:        &crypto.PublicKey{},
	}

	require.False(t, providerKeeper.IsConsumerValidator(ctx, CONSUMER_ID, types.NewProviderConsAddress(validator.ProviderConsAddr)))
	err := providerKeeper.SetConsumerValidator(ctx, CONSUMER_ID, validator)
	require.NoError(t, err)
	require.True(t, providerKeeper.IsConsumerValidator(ctx, CONSUMER_ID, types.NewProviderConsAddress(validator.ProviderConsAddr)))
	providerKeeper.DeleteConsumerValidator(ctx, CONSUMER_ID, types.NewProviderConsAddress(validator.ProviderConsAddr))
	require.False(t, providerKeeper.IsConsumerValidator(ctx, CONSUMER_ID, types.NewProviderConsAddress(validator.ProviderConsAddr)))
}

func TestGetConsumerValSet(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create 3 validators and set them as current validators
	expectedValidators := []types.ConsensusValidator{
		{
			ProviderConsAddr: []byte("providerConsAddr1"),
			Power:            1,
			PublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{1},
				},
			},
		},
		{
			ProviderConsAddr: []byte("providerConsAddr2"),
			Power:            2,
			PublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{2},
				},
			},
		},
		{
			ProviderConsAddr: []byte("providerConsAddr3"),
			Power:            3,
			PublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{3},
				},
			},
		},
	}

	for _, expectedValidator := range expectedValidators {
		err := providerKeeper.SetConsumerValidator(ctx, CONSUMER_ID,
			types.ConsensusValidator{
				ProviderConsAddr: expectedValidator.ProviderConsAddr,
				Power:            expectedValidator.Power,
				PublicKey:        expectedValidator.PublicKey,
			})
		require.NoError(t, err)
	}

	actualValidators, err := providerKeeper.GetConsumerValSet(ctx, CONSUMER_ID)
	require.NoError(t, err)

	// sort validators first to be able to compare
	sortValidators := func(validators []types.ConsensusValidator) {
		sort.Slice(validators, func(i, j int) bool {
			return bytes.Compare(validators[i].ProviderConsAddr, validators[j].ProviderConsAddr) < 0
		})
	}
	sortValidators(expectedValidators)
	sortValidators(actualValidators)
	require.Equal(t, expectedValidators, actualValidators)
}

// createConsumerValidator is a helper function to create a consumer validator with the given `power`. It uses `index` as
// the `ProviderConsAddr` of the validator, and the `seed` to generate the consumer public key. Returns the validator
// and its consumer public key.
func createConsumerValidator(index int, power int64, seed int) (types.ConsensusValidator, crypto.PublicKey) {
	publicKey := cryptotestutil.NewCryptoIdentityFromIntSeed(seed).TMProtoCryptoPublicKey()

	return types.ConsensusValidator{
		ProviderConsAddr: []byte{byte(index)},
		Power:            power,
		PublicKey:        &publicKey,
	}, publicKey
}

// createStakingValidator helper function to generate a validator with the given power and with a provider address based on index
func createStakingValidator(ctx sdk.Context, mocks testkeeper.MockedKeepers, power int64, seed int) stakingtypes.Validator {
	providerConsPubKey := cryptotestutil.NewCryptoIdentityFromIntSeed(seed).TMProtoCryptoPublicKey()

	pk, _ := cryptocodec.FromCmtProtoPublicKey(providerConsPubKey)
	pkAny, _ := codectypes.NewAnyWithValue(pk)
	consAddr := sdk.ConsAddress(pk.Address())
	providerAddr := types.NewProviderConsAddress(consAddr)
	providerValidatorAddr := sdk.ValAddress(providerAddr.Address.Bytes())

	mocks.MockStakingKeeper.EXPECT().
		GetLastValidatorPower(ctx, providerValidatorAddr).Return(power, nil).AnyTimes()

	return stakingtypes.Validator{
		OperatorAddress: providerValidatorAddr.String(),
		ConsensusPubkey: pkAny,
		Status:          stakingtypes.Bonded,
	}
}

func TestDiff(t *testing.T) {
	// In what follows we create 6 validators: A, B, C, D, E, and F where currentValidators = {A, B, C, D, E}
	// and nextValidators = {B, C, D, E, F}. For the validators {B, C, D, E} in the intersection we have:
	// - validator B has no power or consumer key change
	// - validator C has changed its power
	// - validator D has no power change but has changed its consumer key
	// - validator E has both changed its power and its consumer key

	var expectedUpdates []abci.ValidatorUpdate

	// validator A only exists in `currentValidators` and hence an update with 0 power would be generated
	// to remove this validator
	currentA, currentPublicKeyA := createConsumerValidator(1, 1, 1)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: currentPublicKeyA, Power: 0})

	// validator B exists in both `currentValidators` and `nextValidators` but it did not change its
	// power or consumer public key and hence no validator update is generated
	currentB, _ := createConsumerValidator(2, 1, 2)
	nextB, _ := createConsumerValidator(2, 1, 2)

	// validator C exists in both `currentValidators` and `nextValidators` and it changes its power, so
	// a validator update is generated with the new power
	currentC, currentPublicKeyC := createConsumerValidator(3, 1, 3)
	nextC, _ := createConsumerValidator(3, 2, 3)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: currentPublicKeyC, Power: 2})

	// validator D exists in both `currentValidators` and `nextValidators` and it changes its consumer public key, so
	// a validator update is generated to remove the old public key and another update to add the new public key
	currentD, currentPublicKeyD := createConsumerValidator(4, 1, 4)
	nextD, nextPublicKeyD := createConsumerValidator(4, 1, 5)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: currentPublicKeyD, Power: 0})
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: nextPublicKeyD, Power: 1})

	// validator E exists in both `currentValidators` and `nextValidators` and it changes both its power and
	// its consumer public key, so a validator update is generated to remove the old public key and another update to
	// add the new public key with thew new power
	currentE, currentPublicKeyE := createConsumerValidator(5, 1, 6)
	nextE, nextPublicKeyE := createConsumerValidator(5, 2, 7)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: currentPublicKeyE, Power: 0})
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: nextPublicKeyE, Power: 2})

	// validator F does not exist in `currentValidators` and hence an update is generated to add this new validator
	nextF, nextPublicKeyF := createConsumerValidator(6, 1, 8)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: nextPublicKeyF, Power: 1})

	currentValidators := []types.ConsensusValidator{currentA, currentB, currentC, currentD, currentE}
	nextValidators := []types.ConsensusValidator{nextB, nextC, nextD, nextE, nextF}

	actualUpdates := keeper.DiffValidators(currentValidators, nextValidators)

	// sort validators first to be able to compare
	sortUpdates := func(updates []abci.ValidatorUpdate) {
		sort.Slice(updates, func(i, j int) bool {
			if updates[i].Power != updates[j].Power {
				return updates[i].Power < updates[j].Power
			}
			return updates[i].PubKey.String() < updates[j].PubKey.String()
		})
	}

	sortUpdates(expectedUpdates)
	sortUpdates(actualUpdates)
	require.Equal(t, expectedUpdates, actualUpdates)
}

func TestDiffEdgeCases(t *testing.T) {
	require.Empty(t, len(keeper.DiffValidators([]types.ConsensusValidator{}, []types.ConsensusValidator{})))

	valA, publicKeyA := createConsumerValidator(1, 1, 1)
	valB, publicKeyB := createConsumerValidator(2, 2, 2)
	valC, publicKeyC := createConsumerValidator(3, 3, 3)
	validators := []types.ConsensusValidator{valA, valB, valC}

	// we do not expect any validator updates if the `currentValidators` are the same with the `nextValidators`
	require.Empty(t, len(keeper.DiffValidators(validators, validators)))

	// only have `nextValidators` that would generate validator updates for the validators to be added
	expectedUpdates := []abci.ValidatorUpdate{
		{PubKey: publicKeyA, Power: 1},
		{PubKey: publicKeyB, Power: 2},
		{PubKey: publicKeyC, Power: 3},
	}
	actualUpdates := keeper.DiffValidators([]types.ConsensusValidator{}, validators)
	// sort validators first to be able to compare
	sortUpdates := func(updates []abci.ValidatorUpdate) {
		sort.Slice(updates, func(i, j int) bool {
			if updates[i].Power != updates[j].Power {
				return updates[i].Power < updates[j].Power
			}
			return updates[i].PubKey.String() < updates[j].PubKey.String()
		})
	}

	sortUpdates(expectedUpdates)
	sortUpdates(actualUpdates)
	require.Equal(t, expectedUpdates, actualUpdates)

	// only have `currentValidators` that would generate validator updates for the validators to be removed
	expectedUpdates = []abci.ValidatorUpdate{
		{PubKey: publicKeyA, Power: 0},
		{PubKey: publicKeyB, Power: 0},
		{PubKey: publicKeyC, Power: 0},
	}
	actualUpdates = keeper.DiffValidators(validators, []types.ConsensusValidator{})
	sortUpdates(expectedUpdates)
	sortUpdates(actualUpdates)
	require.Equal(t, expectedUpdates, actualUpdates)

	// have nonempty `currentValidators` and `nextValidators`, but with empty intersection
	// all old validators should be removed, all new validators should be added
	expectedUpdates = []abci.ValidatorUpdate{
		{PubKey: publicKeyA, Power: 0},
		{PubKey: publicKeyB, Power: 2},
	}
	actualUpdates = keeper.DiffValidators(validators[0:1], validators[1:2])
	sortUpdates(expectedUpdates)
	sortUpdates(actualUpdates)
	require.Equal(t, expectedUpdates, actualUpdates)
}

func TestSetConsumerValSet(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerID := CONSUMER_ID

	currentValidators := []types.ConsensusValidator{
		{
			ProviderConsAddr: []byte("currentProviderConsAddr1"),
			Power:            2,
			PublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{2},
				},
			},
		},
		{
			ProviderConsAddr: []byte("currentProviderConsAddr2"),
			Power:            3,
			PublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{3},
				},
			},
		},
		{
			ProviderConsAddr: []byte("currentProviderConsAddr3"),
			Power:            4,
			PublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{4},
				},
			},
		},
	}

	nextValidators := []types.ConsensusValidator{
		{
			ProviderConsAddr: []byte("nextProviderConsAddr1"),
			Power:            2,
			PublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{2},
				},
			},
		},
		{
			ProviderConsAddr: []byte("nextProviderConsAddr2"),
			Power:            3,
			PublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{3},
				},
			},
		},
	}

	// set the `currentValidators` for chain `consumerId`
	valSet, err := providerKeeper.GetConsumerValSet(ctx, consumerID)
	require.NoError(t, err)
	require.Empty(t, valSet)
	for _, validator := range currentValidators {
		err := providerKeeper.SetConsumerValidator(ctx, consumerID, validator)
		require.NoError(t, err)
	}

	valSet, err = providerKeeper.GetConsumerValSet(ctx, consumerID)
	require.NoError(t, err)
	require.NotEmpty(t, valSet)

	err = providerKeeper.SetConsumerValSet(ctx, consumerID, nextValidators)
	require.NoError(t, err)
	nextCurrentValidators, err := providerKeeper.GetConsumerValSet(ctx, consumerID)
	require.NoError(t, err)

	// sort validators first to be able to compare
	sortValidators := func(validators []types.ConsensusValidator) {
		sort.Slice(validators, func(i, j int) bool {
			return bytes.Compare(validators[i].ProviderConsAddr, validators[j].ProviderConsAddr) < 0
		})
	}

	sortValidators(nextValidators)
	sortValidators(nextCurrentValidators)
	require.Equal(t, nextValidators, nextCurrentValidators)
}

func TestFilterValidatorsConsiderAll(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerID := CONSUMER_ID

	// no consumer validators returned if we have no bonded validators
	considerAll := func(providerAddr types.ProviderConsAddress) (bool, error) { return true, nil }
	validators, err := providerKeeper.FilterValidators(ctx, consumerID, []stakingtypes.Validator{}, considerAll)
	require.NoError(t, err)
	require.Empty(t, validators)

	var expectedValidators []types.ConsensusValidator

	// create a staking validator A that has not set a consumer public key
	valA := createStakingValidator(ctx, mocks, 1, 1)
	// because validator A has no consumer key set, the `PublicKey` we expect is the key on the provider chain
	valAConsAddr, _ := valA.GetConsAddr()
	valAPublicKey, _ := valA.CmtConsPublicKey()
	expectedValidators = append(expectedValidators, types.ConsensusValidator{
		ProviderConsAddr: types.NewProviderConsAddress(valAConsAddr).Address.Bytes(),
		Power:            1,
		PublicKey:        &valAPublicKey,
	})

	// create a staking validator B that has set a consumer public key
	valB := createStakingValidator(ctx, mocks, 2, 2)
	// validator B has set a consumer key, the `PublicKey` we expect is the key set by `SetValidatorConsumerPubKey`
	valBConsumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	valBConsAddr, _ := valB.GetConsAddr()
	providerKeeper.SetValidatorConsumerPubKey(ctx, consumerID, types.NewProviderConsAddress(valBConsAddr), valBConsumerKey)
	expectedValidators = append(expectedValidators, types.ConsensusValidator{
		ProviderConsAddr: types.NewProviderConsAddress(valBConsAddr).Address.Bytes(),
		Power:            2,
		PublicKey:        &valBConsumerKey,
	})

	bondedValidators := []stakingtypes.Validator{valA, valB}
	actualValidators, err := providerKeeper.FilterValidators(ctx, consumerID, bondedValidators, considerAll)
	require.NoError(t, err)
	require.Equal(t, expectedValidators, actualValidators)
}

func TestFilterValidatorsConsiderOnlyOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerID := CONSUMER_ID

	// no consumer validators returned if we have no opted-in validators
	validators, err := providerKeeper.FilterValidators(ctx, consumerID, []stakingtypes.Validator{},
		func(providerAddr types.ProviderConsAddress) (bool, error) {
			return providerKeeper.IsOptedIn(ctx, consumerID, providerAddr), nil
		})
	require.NoError(t, err)
	require.Empty(t, validators)

	var expectedValidators []types.ConsensusValidator

	// create a staking validator A that has not set a consumer public key
	valA := createStakingValidator(ctx, mocks, 1, 1)
	// because validator A has no consumer key set, the `PublicKey` we expect is the key on the provider chain
	valAConsAddr, _ := valA.GetConsAddr()
	valAPublicKey, _ := valA.CmtConsPublicKey()
	expectedValAConsumerValidator := types.ConsensusValidator{
		ProviderConsAddr: types.NewProviderConsAddress(valAConsAddr).Address.Bytes(),
		Power:            1,
		PublicKey:        &valAPublicKey,
	}
	expectedValidators = append(expectedValidators, expectedValAConsumerValidator)

	// create a staking validator B that has set a consumer public key
	valB := createStakingValidator(ctx, mocks, 2, 2)
	// validator B has set a consumer key, the `PublicKey` we expect is the key set by `SetValidatorConsumerPubKey`
	valBConsumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	valBConsAddr, _ := valB.GetConsAddr()
	providerKeeper.SetValidatorConsumerPubKey(ctx, consumerID, types.NewProviderConsAddress(valBConsAddr), valBConsumerKey)
	expectedValBConsumerValidator := types.ConsensusValidator{
		ProviderConsAddr: types.NewProviderConsAddress(valBConsAddr).Address.Bytes(),
		Power:            2,
		PublicKey:        &valBConsumerKey,
	}
	expectedValidators = append(expectedValidators, expectedValBConsumerValidator)

	// opt in validators A and B with 0 power and no consumer public keys
	providerKeeper.SetOptedIn(ctx, consumerID, types.NewProviderConsAddress(valAConsAddr))
	providerKeeper.SetOptedIn(ctx, consumerID, types.NewProviderConsAddress(valBConsAddr))

	// the expected actual validators are the opted-in validators but with the correct power and consumer public keys set
	bondedValidators := []stakingtypes.Validator{valA, valB}
	actualValidators, err := providerKeeper.FilterValidators(ctx, consumerID, bondedValidators,
		func(providerAddr types.ProviderConsAddress) (bool, error) {
			return providerKeeper.IsOptedIn(ctx, consumerID, providerAddr), nil
		})
	require.NoError(t, err)

	// sort validators first to be able to compare
	sortValidators := func(validators []types.ConsensusValidator) {
		sort.Slice(validators, func(i, j int) bool {
			return bytes.Compare(validators[i].ProviderConsAddr, validators[j].ProviderConsAddr) < 0
		})
	}

	sortValidators(actualValidators)
	sortValidators(expectedValidators)
	require.Equal(t, expectedValidators, actualValidators)

	// create a staking validator C that is not opted in, hence `expectedValidators` remains the same
	valC := createStakingValidator(ctx, mocks, 3, 3)
	bondedValidators = []stakingtypes.Validator{valA, valB, valC}
	actualValidators, err = providerKeeper.FilterValidators(ctx, consumerID, bondedValidators,
		func(providerAddr types.ProviderConsAddress) (bool, error) {
			return providerKeeper.IsOptedIn(ctx, consumerID, providerAddr), nil
		})
	require.NoError(t, err)

	sortValidators(actualValidators)
	sortValidators(expectedValidators)
	require.Equal(t, expectedValidators, actualValidators)
}

func TestCreateConsumerValidator(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerID := CONSUMER_ID

	// create a validator which has set a consumer public key
	valA := createStakingValidator(ctx, mocks, 1, 1)
	valAConsumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	valAConsAddr, _ := valA.GetConsAddr()
	valAProviderConsAddr := types.NewProviderConsAddress(valAConsAddr)
	providerKeeper.SetValidatorConsumerPubKey(ctx, consumerID, valAProviderConsAddr, valAConsumerKey)
	actualConsumerValidatorA, err := providerKeeper.CreateConsumerValidator(ctx, consumerID, valA)
	expectedConsumerValidatorA := types.ConsensusValidator{
		ProviderConsAddr: valAProviderConsAddr.ToSdkConsAddr(),
		Power:            1,
		PublicKey:        &valAConsumerKey,
	}
	require.Equal(t, expectedConsumerValidatorA, actualConsumerValidatorA)
	require.NoError(t, err)

	// create a validator which has not set a consumer public key
	valB := createStakingValidator(ctx, mocks, 2, 2)
	valBConsAddr, _ := valB.GetConsAddr()
	valBProviderConsAddr := types.NewProviderConsAddress(valBConsAddr)
	valBPublicKey, _ := valB.CmtConsPublicKey()
	actualConsumerValidatorB, err := providerKeeper.CreateConsumerValidator(ctx, consumerID, valB)
	expectedConsumerValidatorB := types.ConsensusValidator{
		ProviderConsAddr: valBProviderConsAddr.ToSdkConsAddr(),
		Power:            2,
		PublicKey:        &valBPublicKey,
	}
	require.Equal(t, expectedConsumerValidatorB, actualConsumerValidatorB)
	require.NoError(t, err)
}
