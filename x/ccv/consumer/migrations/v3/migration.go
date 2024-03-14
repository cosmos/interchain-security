package v3

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	consumerKeeper "github.com/cosmos/interchain-security/v5/x/ccv/consumer/keeper"
)

// MigrateParams migrates the consumers module's parameters from the x/params subspace to the
// consumer modules store.
func MigrateParams(ctx sdk.Context, keeper consumerKeeper.Keeper, legacyParamspace paramtypes.Subspace) error {
	params := consumerKeeper.GetConsumerParamsLegacy(ctx, keeper, legacyParamspace)
	err := params.Validate()
	if err != nil {
		return err
	}
	keeper.SetParams(ctx, params)
	keeper.Logger(ctx).Info("successfully migrated provider parameters")
	return nil
}
