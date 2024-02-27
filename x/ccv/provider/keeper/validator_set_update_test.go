package keeper_test

import (
	"bytes"
	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/crypto/ed25519"
	"github.com/cometbft/cometbft/proto/tendermint/crypto"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	cryptotestutil "github.com/cosmos/interchain-security/v4/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
	"sort"
	"testing"
)

// TestEpochValidator tests the `SetEpochValidator`, `IsEpochValidator`, and `DeleteEpochValidator` methods
func TestEpochValidator(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator := types.EpochValidator{
		ProviderConsAddr:  []byte("providerConsAddr"),
		Power:             2,
		ConsumerPublicKey: []byte{3},
	}

	require.False(t, providerKeeper.IsEpochValidator(ctx, "chainID", types.NewProviderConsAddress(validator.ProviderConsAddr)))
	providerKeeper.SetEpochValidator(ctx, "chainID", validator)
	require.True(t, providerKeeper.IsEpochValidator(ctx, "chainID", types.NewProviderConsAddress(validator.ProviderConsAddr)))
	providerKeeper.DeleteEpochValidator(ctx, "chainID", types.NewProviderConsAddress(validator.ProviderConsAddr))
	require.False(t, providerKeeper.IsEpochValidator(ctx, "chainID", types.NewProviderConsAddress(validator.ProviderConsAddr)))
}

func TestGetAllEpochValidators(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create 3 validators and set them as epoch validators
	expectedValidators := []types.EpochValidator{
		{
			ProviderConsAddr:  []byte("providerConsAddr1"),
			Power:             2,
			ConsumerPublicKey: []byte{3},
		},
		{
			ProviderConsAddr:  []byte("providerConsAddr2"),
			Power:             3,
			ConsumerPublicKey: []byte{4},
		},
		{
			ProviderConsAddr:  []byte("providerConsAddr3"),
			Power:             4,
			ConsumerPublicKey: []byte{5},
		},
	}

	for _, expectedValidator := range expectedValidators {
		providerKeeper.SetEpochValidator(ctx, "chainID",
			types.EpochValidator{
				ProviderConsAddr:  expectedValidator.ProviderConsAddr,
				Power:             expectedValidator.Power,
				ConsumerPublicKey: expectedValidator.ConsumerPublicKey})
	}

	actualValidators := providerKeeper.GetAllEpochValidators(ctx, "chainID")

	// sort validators first to be able to compare
	sortValidators := func(validators []types.EpochValidator) {
		sort.Slice(validators, func(i int, j int) bool {
			return bytes.Compare(validators[i].ProviderConsAddr, validators[j].ProviderConsAddr) < 0
		})
	}
	sortValidators(expectedValidators)
	sortValidators(actualValidators)
	require.Equal(t, expectedValidators, actualValidators)
}

// createEpochValidator is a helper function to create an epoch validator with the given `power`. It uses `index` as
// the `ProviderConsAddr` of the validator, and the `seed` to generate the consumer public key. Returns the validator
// and its consumer public key.
func createEpochValidator(index int, power int64, seed int) (types.EpochValidator, crypto.PublicKey) {
	publicKey := cryptotestutil.NewCryptoIdentityFromIntSeed(seed).TMProtoCryptoPublicKey()
	publicKeyBytes, _ := publicKey.Marshal()

	return types.EpochValidator{
		ProviderConsAddr:  []byte{byte(index)},
		Power:             power,
		ConsumerPublicKey: publicKeyBytes}, publicKey
}

func TestComputeNextEpochValidators(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	// helper function to generate a validator with the given power and with a provider address based on index
	createStakingValidator := func(ctx sdk.Context, mocks testkeeper.MockedKeepers, index int, power int64) stakingtypes.Validator {
		providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{byte(index)}).PubKey()
		consAddr := sdk.ConsAddress(providerConsPubKey.Address())
		providerAddr := types.NewProviderConsAddress(consAddr)
		pk, _ := cryptocodec.FromTmPubKeyInterface(providerConsPubKey)
		pkAny, _ := codectypes.NewAnyWithValue(pk)

		var providerValidatorAddr sdk.ValAddress
		providerValidatorAddr = providerAddr.Address.Bytes()

		mocks.MockStakingKeeper.EXPECT().
			GetLastValidatorPower(ctx, providerValidatorAddr).Return(power).AnyTimes()

		return stakingtypes.Validator{
			OperatorAddress: providerValidatorAddr.String(),
			ConsensusPubkey: pkAny,
		}
	}

	// no epoch validators returned if we have no bonded validators
	require.Empty(t, providerKeeper.ComputeNextEpochValidators(ctx, chainID, []stakingtypes.Validator{}))

	var expectedEpochValidators []types.EpochValidator

	// create a staking validator A that has not set a consumer public key
	valA := createStakingValidator(ctx, mocks, 1, 1)
	// because validator A has no consumer key set, the `ConsumerPublicKey` we expect is the key on the provider chain
	valAConsAddr, _ := valA.GetConsAddr()
	valAPublicKey, _ := valA.TmConsPublicKey()
	valAPublicKeyBytes, _ := valAPublicKey.Marshal()
	expectedEpochValidators = append(expectedEpochValidators, types.EpochValidator{
		ProviderConsAddr:  types.NewProviderConsAddress(valAConsAddr).Address.Bytes(),
		Power:             1,
		ConsumerPublicKey: valAPublicKeyBytes,
	})

	// create a staking validator B that has set a consumer public key
	valB := createStakingValidator(ctx, mocks, 2, 2)
	// validator B has set a consumer key, the `ConsumerPublicKey` we expect is the key set by `SetValidatorConsumerPubKey`
	valBConsumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	valBConsumerKeyBytes, _ := valBConsumerKey.Marshal()
	valBConsAddr, _ := valB.GetConsAddr()
	providerKeeper.SetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(valBConsAddr), valBConsumerKey)
	expectedEpochValidators = append(expectedEpochValidators, types.EpochValidator{
		ProviderConsAddr:  types.NewProviderConsAddress(valBConsAddr).Address.Bytes(),
		Power:             2,
		ConsumerPublicKey: valBConsumerKeyBytes,
	})

	bondedValidators := []stakingtypes.Validator{valA, valB}
	actualEpochValidators := providerKeeper.ComputeNextEpochValidators(ctx, "chainID", bondedValidators)
	require.Equal(t, expectedEpochValidators, actualEpochValidators)
}

func TestDiff(t *testing.T) {
	// In what follows we create 6 validators: A, B, C, D, E, and F where currentValidators = {A, B, C, D, E}
	// and nextValidators = {B, C, D, E, F}. For the validators {B, C, D, E} in the intersection we have:
	// - validator B has no power or consumer key change
	// - validator C has changed its power
	// - validator E has no power change but has changed its consumer key
	// - validator F has both changed its power and its consumer key

	var expectedUpdates []abci.ValidatorUpdate

	// validator A only exists in `currentValidators` and hence an update with 0 power would be generated
	// to remove this validator
	currentA, currentPublicKeyA := createEpochValidator(1, 1, 1)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: currentPublicKeyA, Power: 0})

	// validator B exists in both `currentValidators` and `nextValidators` but it did not change its
	// power or consumer public key and hence no validator update is generated
	currentB, _ := createEpochValidator(2, 1, 2)
	nextB, _ := createEpochValidator(2, 1, 2)

	// validator C exists in both `currentValidators` and `nextValidators` and it changes its power, so
	// a validator update is generated with the new power
	currentC, currentPublicKeyC := createEpochValidator(3, 1, 3)
	nextC, _ := createEpochValidator(3, 2, 3)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: currentPublicKeyC, Power: 2})

	// validator D exists in both `currentValidators` and `nextValidators` and it changes its consumer public key, so
	// a validator update is generated to remove the old public key and another update to add the new public key
	currentD, currentPublicKeyD := createEpochValidator(4, 1, 4)
	nextD, nextPublicKeyD := createEpochValidator(4, 1, 5)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: currentPublicKeyD, Power: 0})
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: nextPublicKeyD, Power: 1})

	// validator E exists in both `currentValidators` and `nextValidators` and it changes both its power and
	// its consumer public key, so a validator update is generated to remove the old public key and another update to
	// add the new public key with thew new power
	currentE, currentPublicKeyE := createEpochValidator(5, 1, 6)
	nextE, nextPublicKeyE := createEpochValidator(5, 2, 7)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: currentPublicKeyE, Power: 0})
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: nextPublicKeyE, Power: 2})

	// validator F does not exist in `currentValidators` and hence an update is generated to add this new validator
	nextF, nextPublicKeyF := createEpochValidator(6, 1, 8)
	expectedUpdates = append(expectedUpdates, abci.ValidatorUpdate{PubKey: nextPublicKeyF, Power: 1})

	currentValidators := []types.EpochValidator{currentA, currentB, currentC, currentD, currentE}
	nextValidators := []types.EpochValidator{nextB, nextC, nextD, nextE, nextF}

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
	require.Empty(t, len(keeper.DiffValidators([]types.EpochValidator{}, []types.EpochValidator{})))

	valA, publicKeyA := createEpochValidator(1, 1, 1)
	valB, publicKeyB := createEpochValidator(2, 2, 2)
	valC, publicKeyC := createEpochValidator(3, 3, 3)
	validators := []types.EpochValidator{valA, valB, valC}

	// we do not expect any validator updates if the `currentValidators` are the same with the `nextValidators`
	require.Empty(t, len(keeper.DiffValidators(validators, validators)))

	// only have `nextValidators` that would generate validator updates for the validators to be added
	expectedUpdates := []abci.ValidatorUpdate{{publicKeyA, 1}, {publicKeyB, 2}, {publicKeyC, 3}}
	actualUpdates := keeper.DiffValidators([]types.EpochValidator{}, validators)
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
	expectedUpdates = []abci.ValidatorUpdate{{publicKeyA, 0}, {publicKeyB, 0}, {publicKeyC, 0}}
	actualUpdates = keeper.DiffValidators(validators, []types.EpochValidator{})
	sortUpdates(expectedUpdates)
	sortUpdates(actualUpdates)
	require.Equal(t, expectedUpdates, actualUpdates)
}

func TestResetCurrentEpochValidators(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	currentValidators := []types.EpochValidator{
		{
			ProviderConsAddr:  []byte("currentProviderConsAddr1"),
			Power:             2,
			ConsumerPublicKey: []byte{3},
		},
		{
			ProviderConsAddr:  []byte("currentProviderConsAddr2"),
			Power:             3,
			ConsumerPublicKey: []byte{4},
		},
		{
			ProviderConsAddr:  []byte("currentProviderConsAddr3"),
			Power:             4,
			ConsumerPublicKey: []byte{5},
		},
	}

	nextValidators := []types.EpochValidator{
		{
			ProviderConsAddr:  []byte("nextProviderConsAddr1"),
			Power:             2,
			ConsumerPublicKey: []byte{3},
		},
		{
			ProviderConsAddr:  []byte("nextProviderConsAddr2"),
			Power:             3,
			ConsumerPublicKey: []byte{4},
		},
	}

	// set the `currentValidators` as epoch validators
	require.Empty(t, providerKeeper.GetAllEpochValidators(ctx, chainID))
	for _, validator := range currentValidators {
		providerKeeper.SetEpochValidator(ctx, chainID, validator)
	}
	require.NotEmpty(t, providerKeeper.GetAllEpochValidators(ctx, chainID))

	providerKeeper.ResetCurrentEpochValidators(ctx, chainID, nextValidators)
	nextCurrentValidators := providerKeeper.GetAllEpochValidators(ctx, chainID)

	// sort validators first to be able to compare
	sortValidators := func(validators []types.EpochValidator) {
		sort.Slice(validators, func(i, j int) bool {
			return bytes.Compare(validators[i].ProviderConsAddr, validators[j].ProviderConsAddr) < 0
		})
	}

	sortValidators(nextValidators)
	sortValidators(nextCurrentValidators)
	require.Equal(t, nextValidators, nextCurrentValidators)
}
