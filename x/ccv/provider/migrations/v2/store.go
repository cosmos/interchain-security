package v2

import (
	"github.com/cosmos/cosmos-sdk/codec"
	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func MigrateStore(ctx sdk.Context, storeKey storetypes.StoreKey, cdc codec.BinaryCodec, paramSpace paramtypes.Subspace,
	initSlashMeterFn func()) error {
	migrateParamsStore(ctx, paramSpace)
	// Initializes the slash meter (SlashMeterKey) and sets the last replenish time (LastSlashMeterReplenishTimeKey)
	// It must be called after migrateParamsStore since it uses param added in this fn
	initSlashMeterFn()

	return nil
}

func migrateParamsStore(ctx sdk.Context, paramSpace paramtypes.Subspace) {
	if !paramSpace.HasKeyTable() {
		paramSpace.WithKeyTable(providertypes.ParamKeyTable())
	}

	paramSpace.Set(ctx, providertypes.KeySlashMeterReplenishPeriod, providertypes.DefaultSlashMeterReplenishPeriod)
	paramSpace.Set(ctx, providertypes.KeySlashMeterReplenishFraction, providertypes.DefaultSlashMeterReplenishFraction)
	paramSpace.Set(ctx, providertypes.KeyMaxPendingSlashPackets, int64(providertypes.DefaultMaxPendingSlashPackets))
}
