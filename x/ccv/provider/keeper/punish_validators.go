package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
)

// JailAndTombstoneValidator jails and tombstones the validator for the given provider consensus chain address
func (k Keeper) JailAndTombstoneValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress, chainID string) {
	logger := k.Logger(ctx)

	// get validator
	val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !ok || val.IsUnbonded() {
		logger.Error("validator not found or is unbonded", providerAddr.String())
		return
	}

	// tombstone validator if not already
	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		k.Logger(ctx).Info("validator is already tombstoned", "provider cons addr", providerAddr.String())
		return
	}

	// jail validator if not already
	if !val.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerAddr.ToSdkConsAddr())
	}

	// update jail time to end after double sign jail duration
	k.slashingKeeper.JailUntil(ctx, providerAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime)
	// tombstone validator
	k.slashingKeeper.Tombstone(ctx, providerAddr.ToSdkConsAddr())
}
