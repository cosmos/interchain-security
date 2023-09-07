package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
)

// JailAndTombstoneValidator jails the validator with the given provider consensus address
// Note that the tombstoning is temporarily removed until we slash validator
// for double signing on a consumer chain, see comment
// https://github.com/cosmos/interchain-security/pull/1232#issuecomment-1693127641.
func (k Keeper) JailAndTombstoneValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress) {
	logger := k.Logger(ctx)

	// get validator
	val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !ok || val.IsUnbonded() {
		logger.Error("validator not found or is unbonded", providerAddr.String())
		return
	}

	// check that the validator isn't tombstoned
	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		logger.Info("validator is already tombstoned", "provider cons addr", providerAddr.String())
		return
	}

	// jail validator if not already
	if !val.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerAddr.ToSdkConsAddr())
	}

	// update jail time to end after double sign jail duration
	k.slashingKeeper.JailUntil(ctx, providerAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime)

	// TODO: do we need to jail if we tombstone, that's what cosmos-sdk does
	k.slashingKeeper.Tombstone(ctx, providerAddr.ToSdkConsAddr())
}
