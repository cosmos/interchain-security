package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
)

// JailAndTombstoneByConsumerAddress jails and tombstones the validator assigned to the given consumer chain address
func (k Keeper) JailAndTombstoneByConsumerAddress(ctx sdk.Context, consumerAddr types.ConsumerConsAddress, chainID string) error {
	logger := k.Logger(ctx)

	// jail and tombstone the Byzantine validators
	providerAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerAddr)
	val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())

	if !ok || val.IsUnbonded() {
		logger.Error("validator not found or is unbonded", providerAddr.String())
	}

	// jail validator if not already
	if !val.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerAddr.ToSdkConsAddr())
	}

	// tombstone validator if not already
	if !k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		k.slashingKeeper.Tombstone(ctx, providerAddr.ToSdkConsAddr())
		k.Logger(ctx).Info("validator tombstoned", "provider cons addr", providerAddr.String())
	}

	// update jail time to end after double sign jail duration
	k.slashingKeeper.JailUntil(ctx, providerAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime)

	return nil
}
