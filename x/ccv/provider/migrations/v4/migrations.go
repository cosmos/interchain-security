package v4

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// MigrateParams adds missing provider chain params to the param store.
func MigrateParams(ctx sdk.Context, paramsSubspace paramtypes.Subspace) {
	if paramsSubspace.HasKeyTable() {
		paramsSubspace.Set(ctx, providertypes.KeyBlocksPerEpoch, providertypes.DefaultBlocksPerEpoch)
	} else {
		paramsSubspace.WithKeyTable(providertypes.ParamKeyTable())
		paramsSubspace.Set(ctx, providertypes.KeyBlocksPerEpoch, providertypes.DefaultBlocksPerEpoch)
	}
}
