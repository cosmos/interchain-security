package v3

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/module"
	upgradetypes "github.com/cosmos/cosmos-sdk/x/upgrade/types"
)

// Note: ensure these values are properly set before running upgrade
var (
	UpgradeName = "v3"
)

// CreateUpgradeHandler creates an SDK upgrade handler for v3
func CreateUpgradeHandler(
	mm *module.Manager,
	configurator module.Configurator,
) upgradetypes.UpgradeHandler {
	return func(ctx sdk.Context, _ upgradetypes.Plan, vm module.VersionMap) (module.VersionMap, error) {
		newVm, err := mm.RunMigrations(ctx, configurator, vm)
		if err != nil {
			return newVm, err
		}
		return newVm, nil
	}
}
