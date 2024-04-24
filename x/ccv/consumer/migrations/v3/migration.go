package v3

import (
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"

	storetypes "cosmossdk.io/store/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
)

// MigrateLegacyParams migrates the consumers module's parameters from the x/params subspace to the
// consumer modules store.
func MigrateLegacyParams(ctx sdk.Context, cdc codec.BinaryCodec, store storetypes.KVStore, legacyParamspace ParamSubspace) error {
	params := GetConsumerParamsLegacy(ctx, legacyParamspace)
	err := params.Validate()
	if err != nil {
		return err
	}

	bz := cdc.MustMarshal(&params)
	store.Set(types.ParametersKey(), bz)
	ctx.Logger().Info("successfully migrated consumer parameters")
	return nil
}
