package keeper_test

import (
	"testing"

	"cosmossdk.io/math"
	"github.com/cometbft/cometbft/proto/tendermint/crypto"
	"github.com/stretchr/testify/require"

	testkeeper "github.com/cosmos/interchain-security/v6/testutil/keeper"
	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
)

func TestSetLastProviderConsensusValidator(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddr"),
		Power:            2,
		PublicKey:        &crypto.PublicKey{},
	}

	providerKeeper.SetLastProviderConsensusValidator(ctx, validator)

	// Retrieve the stored validator
	vals, err := providerKeeper.GetLastProviderConsensusValSet(ctx)
	require.NoError(t, err, "failed to get stored validator")

	storedValidator := vals[0]
	require.Equal(t, validator, storedValidator, "stored validator does not match")
}

func TestSetLastProviderConsensusValSet(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator1 := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddr1"),
		Power:            2,
		PublicKey:        &crypto.PublicKey{},
	}

	validator2 := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddr2"),
		Power:            3,
		PublicKey:        &crypto.PublicKey{},
	}

	nextValidators := []types.ConsensusValidator{validator1, validator2}

	providerKeeper.SetLastProviderConsensusValSet(ctx, nextValidators)

	// Retrieve the stored validator set
	storedValidators, err := providerKeeper.GetLastProviderConsensusValSet(ctx)
	require.NoError(t, err, "failed to get stored validator set")
	require.Equal(t, nextValidators, storedValidators, "stored validator set does not match")
}

func TestDeleteLastProviderConsensusValidator(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddr"),
		Power:            2,
		PublicKey:        &crypto.PublicKey{},
	}

	providerKeeper.SetLastProviderConsensusValidator(ctx, validator)

	// Delete the stored validator
	providerKeeper.DeleteLastProviderConsensusValidator(ctx, types.NewProviderConsAddress(validator.ProviderConsAddr))

	// Ensure the validator is deleted
	storedValidators, err := providerKeeper.GetLastProviderConsensusValSet(ctx)
	require.NoError(t, err, "failed to get stored validator set")
	require.Empty(t, storedValidators, "validator set should be empty")
}

func TestDeleteLastProviderConsensusValSet(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator1 := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddr1"),
		Power:            2,
		PublicKey:        &crypto.PublicKey{},
	}

	validator2 := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddr2"),
		Power:            3,
		PublicKey:        &crypto.PublicKey{},
	}

	nextValidators := []types.ConsensusValidator{validator1, validator2}

	providerKeeper.SetLastProviderConsensusValSet(ctx, nextValidators)

	// check that the set is not empty
	storedValidators, err := providerKeeper.GetLastProviderConsensusValSet(ctx)
	require.NoError(t, err, "failed to get stored validator set")
	require.NotEmpty(t, storedValidators, "validator set should not be empty")

	// Delete the stored validator set
	providerKeeper.DeleteLastProviderConsensusValSet(ctx)

	// Ensure the validator set is empty
	storedValidators, err = providerKeeper.GetLastProviderConsensusValSet(ctx)
	require.NoError(t, err, "failed to get stored validator set")
	require.Empty(t, storedValidators, "validator set should be empty")
}

func TestGetLastTotalProviderConsensusPower(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	validator1 := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddr1"),
		Power:            2,
		PublicKey:        &crypto.PublicKey{},
	}
	validator2 := types.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddr2"),
		Power:            3,
		PublicKey:        &crypto.PublicKey{},
	}
	nextValidators := []types.ConsensusValidator{validator1, validator2}
	providerKeeper.SetLastProviderConsensusValSet(ctx, nextValidators)
	// Get the total power of the last stored validator set
	totalPower, err := providerKeeper.GetLastTotalProviderConsensusPower(ctx)
	require.NoError(t, err, "failed to get total power")
	expectedTotalPower := math.NewInt(5)
	require.Equal(t, expectedTotalPower, totalPower, "total power does not match")
}
