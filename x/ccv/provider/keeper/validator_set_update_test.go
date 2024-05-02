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
	"github.com/cometbft/cometbft/crypto/ed25519"
	"github.com/cometbft/cometbft/proto/tendermint/crypto"

	cryptotestutil "github.com/cosmos/interchain-security/v4/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// TestConsumerValidator tests the `SetConsumerValidator`, `IsConsumerValidator`, and `DeleteConsumerValidator` methods
func TestConsumerValidator(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator := types.ConsumerValidator{
		ProviderConsAddr:  []byte("providerConsAddr"),
		Power:             2,
		ConsumerPublicKey: &crypto.PublicKey{},
	}

	require.False(t, providerKeeper.IsConsumerValidator(ctx, "chainID", types.NewProviderConsAddress(validator.ProviderConsAddr)))
	providerKeeper.SetConsumerValidator(ctx, "chainID", validator)
	require.True(t, providerKeeper.IsConsumerValidator(ctx, "chainID", types.NewProviderConsAddress(validator.ProviderConsAddr)))
	providerKeeper.DeleteConsumerValidator(ctx, "chainID", types.NewProviderConsAddress(validator.ProviderConsAddr))
	require.False(t, providerKeeper.IsConsumerValidator(ctx, "chainID", types.NewProviderConsAddress(validator.ProviderConsAddr)))
}

func TestGetConsumerValSet(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create 3 validators and set them as current validators
	expectedValidators := []types.ConsumerValidator{
		{
			ProviderConsAddr: []byte("providerConsAddr1"),
			Power:            1,
			ConsumerPublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{1},
				},
			},
		},
		{
			ProviderConsAddr: []byte("providerConsAddr2"),
			Power:            2,
			ConsumerPublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{2},
				},
			},
		},
		{
			ProviderConsAddr: []byte("providerConsAddr3"),
			Power:            3,
			ConsumerPublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{3},
				},
			},
		},
	}

	for _, expectedValidator := range expectedValidators {
		providerKeeper.SetConsumerValidator(ctx, "chainID",
			types.ConsumerValidator{
				ProviderConsAddr:  expectedValidator.ProviderConsAddr,
				Power:             expectedValidator.Power,
				ConsumerPublicKey: expectedValidator.ConsumerPublicKey,
			})
	}

	actualValidators := providerKeeper.GetConsumerValSet(ctx, "chainID")

	// sort validators first to be able to compare
	sortValidators := func(validators []types.ConsumerValidator) {
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
func createConsumerValidator(index int, power int64, seed int) (types.ConsumerValidator, crypto.PublicKey) {
	publicKey := cryptotestutil.NewCryptoIdentityFromIntSeed(seed).TMProtoCryptoPublicKey()

	return types.ConsumerValidator{
		ProviderConsAddr:  []byte{byte(index)},
		Power:             power,
		ConsumerPublicKey: &publicKey,
	}, publicKey
}

// createStakingValidator helper function to generate a validator with the given power and with a provider address based on index
func createStakingValidator(ctx sdk.Context, mocks testkeeper.MockedKeepers, index int, power int64) stakingtypes.Validator {
	providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{byte(index)}).PubKey()
	consAddr := sdk.ConsAddress(providerConsPubKey.Address())
	providerAddr := types.NewProviderConsAddress(consAddr)
	pk, _ := cryptocodec.FromTmPubKeyInterface(providerConsPubKey)
	pkAny, _ := codectypes.NewAnyWithValue(pk)
	providerValidatorAddr := sdk.ValAddress(providerAddr.Address.Bytes())

	mocks.MockStakingKeeper.EXPECT().
		GetLastValidatorPower(ctx, providerValidatorAddr).Return(power).AnyTimes()

	return stakingtypes.Validator{
		OperatorAddress: providerValidatorAddr.String(),
		ConsensusPubkey: pkAny,
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

	currentValidators := []types.ConsumerValidator{currentA, currentB, currentC, currentD, currentE}
	nextValidators := []types.ConsumerValidator{nextB, nextC, nextD, nextE, nextF}

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
	require.Empty(t, len(keeper.DiffValidators([]types.ConsumerValidator{}, []types.ConsumerValidator{})))

	valA, publicKeyA := createConsumerValidator(1, 1, 1)
	valB, publicKeyB := createConsumerValidator(2, 2, 2)
	valC, publicKeyC := createConsumerValidator(3, 3, 3)
	validators := []types.ConsumerValidator{valA, valB, valC}

	// we do not expect any validator updates if the `currentValidators` are the same with the `nextValidators`
	require.Empty(t, len(keeper.DiffValidators(validators, validators)))

	// only have `nextValidators` that would generate validator updates for the validators to be added
	expectedUpdates := []abci.ValidatorUpdate{
		{PubKey: publicKeyA, Power: 1},
		{PubKey: publicKeyB, Power: 2},
		{PubKey: publicKeyC, Power: 3},
	}
	actualUpdates := keeper.DiffValidators([]types.ConsumerValidator{}, validators)
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
	actualUpdates = keeper.DiffValidators(validators, []types.ConsumerValidator{})
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

	chainID := "chainID"

	currentValidators := []types.ConsumerValidator{
		{
			ProviderConsAddr: []byte("currentProviderConsAddr1"),
			Power:            2,
			ConsumerPublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{2},
				},
			},
		},
		{
			ProviderConsAddr: []byte("currentProviderConsAddr2"),
			Power:            3,
			ConsumerPublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{3},
				},
			},
		},
		{
			ProviderConsAddr: []byte("currentProviderConsAddr3"),
			Power:            4,
			ConsumerPublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{4},
				},
			},
		},
	}

	nextValidators := []types.ConsumerValidator{
		{
			ProviderConsAddr: []byte("nextProviderConsAddr1"),
			Power:            2,
			ConsumerPublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{2},
				},
			},
		},
		{
			ProviderConsAddr: []byte("nextProviderConsAddr2"),
			Power:            3,
			ConsumerPublicKey: &crypto.PublicKey{
				Sum: &crypto.PublicKey_Ed25519{
					Ed25519: []byte{3},
				},
			},
		},
	}

	// set the `currentValidators` for chain `chainID`
	require.Empty(t, providerKeeper.GetConsumerValSet(ctx, chainID))
	for _, validator := range currentValidators {
		providerKeeper.SetConsumerValidator(ctx, chainID, validator)
	}
	require.NotEmpty(t, providerKeeper.GetConsumerValSet(ctx, chainID))

	providerKeeper.SetConsumerValSet(ctx, chainID, nextValidators)
	nextCurrentValidators := providerKeeper.GetConsumerValSet(ctx, chainID)

	// sort validators first to be able to compare
	sortValidators := func(validators []types.ConsumerValidator) {
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

	chainID := "chainID"

	// no consumer validators returned if we have no bonded validators
	considerAll := func(providerAddr types.ProviderConsAddress) bool { return true }
	require.Empty(t, providerKeeper.FilterValidators(ctx, chainID, []stakingtypes.Validator{}, considerAll))

	var expectedValidators []types.ConsumerValidator

	// create a staking validator A that has not set a consumer public key
	valA := createStakingValidator(ctx, mocks, 1, 1)
	// because validator A has no consumer key set, the `ConsumerPublicKey` we expect is the key on the provider chain
	valAConsAddr, _ := valA.GetConsAddr()
	valAPublicKey, _ := valA.TmConsPublicKey()
	expectedValidators = append(expectedValidators, types.ConsumerValidator{
		ProviderConsAddr:  types.NewProviderConsAddress(valAConsAddr).Address.Bytes(),
		Power:             1,
		ConsumerPublicKey: &valAPublicKey,
	})

	// create a staking validator B that has set a consumer public key
	valB := createStakingValidator(ctx, mocks, 2, 2)
	// validator B has set a consumer key, the `ConsumerPublicKey` we expect is the key set by `SetValidatorConsumerPubKey`
	valBConsumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	valBConsAddr, _ := valB.GetConsAddr()
	providerKeeper.SetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(valBConsAddr), valBConsumerKey)
	expectedValidators = append(expectedValidators, types.ConsumerValidator{
		ProviderConsAddr:  types.NewProviderConsAddress(valBConsAddr).Address.Bytes(),
		Power:             2,
		ConsumerPublicKey: &valBConsumerKey,
	})

	bondedValidators := []stakingtypes.Validator{valA, valB}
	actualValidators := providerKeeper.FilterValidators(ctx, chainID, bondedValidators, considerAll)
	require.Equal(t, expectedValidators, actualValidators)
}

func TestFilterValidatorsConsiderOnlyOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	// no consumer validators returned if we have no opted-in validators
	require.Empty(t, providerKeeper.FilterValidators(ctx, chainID, []stakingtypes.Validator{},
		func(providerAddr types.ProviderConsAddress) bool {
			return providerKeeper.IsOptedIn(ctx, chainID, providerAddr)
		}))

	var expectedValidators []types.ConsumerValidator

	// create a staking validator A that has not set a consumer public key
	valA := createStakingValidator(ctx, mocks, 1, 1)
	// because validator A has no consumer key set, the `ConsumerPublicKey` we expect is the key on the provider chain
	valAConsAddr, _ := valA.GetConsAddr()
	valAPublicKey, _ := valA.TmConsPublicKey()
	expectedValAConsumerValidator := types.ConsumerValidator{
		ProviderConsAddr:  types.NewProviderConsAddress(valAConsAddr).Address.Bytes(),
		Power:             1,
		ConsumerPublicKey: &valAPublicKey,
	}
	expectedValidators = append(expectedValidators, expectedValAConsumerValidator)

	// create a staking validator B that has set a consumer public key
	valB := createStakingValidator(ctx, mocks, 2, 2)
	// validator B has set a consumer key, the `ConsumerPublicKey` we expect is the key set by `SetValidatorConsumerPubKey`
	valBConsumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	valBConsAddr, _ := valB.GetConsAddr()
	providerKeeper.SetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(valBConsAddr), valBConsumerKey)
	expectedValBConsumerValidator := types.ConsumerValidator{
		ProviderConsAddr:  types.NewProviderConsAddress(valBConsAddr).Address.Bytes(),
		Power:             2,
		ConsumerPublicKey: &valBConsumerKey,
	}
	expectedValidators = append(expectedValidators, expectedValBConsumerValidator)

	// opt in validators A and B with 0 power and no consumer public keys
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(valAConsAddr))
	providerKeeper.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(valBConsAddr))

	// the expected actual validators are the opted-in validators but with the correct power and consumer public keys set
	bondedValidators := []stakingtypes.Validator{valA, valB}
	actualValidators := providerKeeper.FilterValidators(ctx, "chainID", bondedValidators,
		func(providerAddr types.ProviderConsAddress) bool {
			return providerKeeper.IsOptedIn(ctx, chainID, providerAddr)
		})

	// sort validators first to be able to compare
	sortValidators := func(validators []types.ConsumerValidator) {
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
	actualValidators = providerKeeper.FilterValidators(ctx, "chainID", bondedValidators,
		func(providerAddr types.ProviderConsAddress) bool {
			return providerKeeper.IsOptedIn(ctx, chainID, providerAddr)
		})

	sortValidators(actualValidators)
	sortValidators(expectedValidators)
	require.Equal(t, expectedValidators, actualValidators)
}

func TestCreateConsumerValidator(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	// create a validator which has set a consumer public key
	valA := createStakingValidator(ctx, mocks, 0, 1)
	valAConsumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	valAConsAddr, _ := valA.GetConsAddr()
	valAProviderConsAddr := types.NewProviderConsAddress(valAConsAddr)
	providerKeeper.SetValidatorConsumerPubKey(ctx, chainID, valAProviderConsAddr, valAConsumerKey)
	actualConsumerValidatorA, err := providerKeeper.CreateConsumerValidator(ctx, chainID, valA)
	expectedConsumerValidatorA := types.ConsumerValidator{
		ProviderConsAddr:  valAProviderConsAddr.ToSdkConsAddr(),
		Power:             1,
		ConsumerPublicKey: &valAConsumerKey,
	}
	require.Equal(t, expectedConsumerValidatorA, actualConsumerValidatorA)
	require.NoError(t, err)

	// create a validator which has not set a consumer public key
	valB := createStakingValidator(ctx, mocks, 1, 2)
	valBConsAddr, _ := valB.GetConsAddr()
	valBProviderConsAddr := types.NewProviderConsAddress(valBConsAddr)
	valBPublicKey, _ := valB.TmConsPublicKey()
	actualConsumerValidatorB, err := providerKeeper.CreateConsumerValidator(ctx, chainID, valB)
	expectedConsumerValidatorB := types.ConsumerValidator{
		ProviderConsAddr:  valBProviderConsAddr.ToSdkConsAddr(),
		Power:             2,
		ConsumerPublicKey: &valBPublicKey,
	}
	require.Equal(t, expectedConsumerValidatorB, actualConsumerValidatorB)
	require.NoError(t, err)
}
