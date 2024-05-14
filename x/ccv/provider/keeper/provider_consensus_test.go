package keeper_test

import (
	"testing"

	"github.com/cometbft/cometbft/proto/tendermint/crypto"
	"github.com/stretchr/testify/require"

	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

func TestSetLastProviderConsensusValidator(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator := types.ConsumerValidator{
		ProviderConsAddr:  []byte("providerConsAddr"),
		Power:             2,
		ConsumerPublicKey: &crypto.PublicKey{},
	}

	providerKeeper.SetLastProviderConsensusValidator(ctx, validator)

	// Retrieve the stored validator
	storedValidator := providerKeeper.GetLastProviderConsensusValSet(ctx)[0]

	require.Equal(t, validator, storedValidator, "stored validator does not match")
}

func TestSetLastProviderConsensusValSet(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator1 := types.ConsumerValidator{
		ProviderConsAddr:  []byte("providerConsAddr1"),
		Power:             2,
		ConsumerPublicKey: &crypto.PublicKey{},
	}

	validator2 := types.ConsumerValidator{
		ProviderConsAddr:  []byte("providerConsAddr2"),
		Power:             3,
		ConsumerPublicKey: &crypto.PublicKey{},
	}

	nextValidators := []types.ConsumerValidator{validator1, validator2}

	providerKeeper.SetLastProviderConsensusValSet(ctx, nextValidators)

	// Retrieve the stored validator set
	storedValidators := providerKeeper.GetLastProviderConsensusValSet(ctx)
	require.Equal(t, nextValidators, storedValidators, "stored validator set does not match")
}

func TestDeleteLastProviderConsensusValidator(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator := types.ConsumerValidator{
		ProviderConsAddr:  []byte("providerConsAddr"),
		Power:             2,
		ConsumerPublicKey: &crypto.PublicKey{},
	}

	providerKeeper.SetLastProviderConsensusValidator(ctx, validator)

	// Delete the stored validator
	providerKeeper.DeleteLastProviderConsensusValidator(ctx, types.NewProviderConsAddress(validator.ProviderConsAddr))

	// Ensure the validator is deleted
	storedValidators := providerKeeper.GetLastProviderConsensusValSet(ctx)
	require.Empty(t, storedValidators, "validator set should be empty")
}

func TestDeleteLastProviderConsensusValSet(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validator1 := types.ConsumerValidator{
		ProviderConsAddr:  []byte("providerConsAddr1"),
		Power:             2,
		ConsumerPublicKey: &crypto.PublicKey{},
	}

	validator2 := types.ConsumerValidator{
		ProviderConsAddr:  []byte("providerConsAddr2"),
		Power:             3,
		ConsumerPublicKey: &crypto.PublicKey{},
	}

	nextValidators := []types.ConsumerValidator{validator1, validator2}

	providerKeeper.SetLastProviderConsensusValSet(ctx, nextValidators)

	// Delete the stored validator set
	providerKeeper.DeleteLastProviderConsensusValSet(ctx)

	// Ensure the validator set is empty
	storedValidators := providerKeeper.GetLastProviderConsensusValSet(ctx)
	require.Empty(t, storedValidators, "validator set should be empty")
}
