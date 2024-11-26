package v9

import (
	"time"

	"cosmossdk.io/math"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v6/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
)

func MigrateConsumerInfractionParams(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) error {
	infractionParameters := defaultInfractionParams()

	activeConsumerIds := pk.GetAllActiveConsumerIds(ctx)
	for _, consumerId := range activeConsumerIds {
		if err := pk.SetInfractionParameters(ctx, consumerId, infractionParameters); err != nil {
			return err
		}
	}

	return nil
}

func defaultInfractionParams() providertypes.InfractionParameters {
	return providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  time.Duration(1<<63 - 1),        // the largest value a time.Duration can hold 9223372036854775807 (approximately 292 years)
			SlashFraction: math.LegacyNewDecWithPrec(5, 2), // 0.05
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  600 * time.Second,
			SlashFraction: math.LegacyNewDec(0), // no slashing for downtime on the consumer
		},
	}
}
