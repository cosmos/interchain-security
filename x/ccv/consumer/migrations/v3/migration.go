package v3

import (
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"

	storetypes "cosmossdk.io/store/types"

	consumertypes "github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// MigrateLegacyParams migrates the consumers module's parameters from the x/params subspace to the
// consumer modules store.
func MigrateLegacyParams(ctx sdk.Context, cdc codec.BinaryCodec, store storetypes.KVStore, legacyParamspace ccvtypes.LegacyParamSubspace) error {
	ctx.Logger().Info("starting consumer legacy params migration")
	params := GetConsumerParamsLegacy(ctx, legacyParamspace)
	err := params.Validate()
	if err != nil {
		return err
	}

	bz := cdc.MustMarshal(&params)
	store.Set(consumertypes.ParametersKey(), bz)
	ctx.Logger().Info("successfully migrated consumer parameters")
	return nil
}
