package keeper

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	providertypes "github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
)

// Migrator is a struct for handling in-place store migrations.
type Migrator struct {
	ccvProviderKeeper     Keeper
	ccvProviderParamSpace paramtypes.Subspace
}

// NewMigrator returns a new Migrator.
func NewMigrator(ccvProviderKeeper Keeper, ccvProviderParamSpace paramtypes.Subspace,
) Migrator {
	return Migrator{ccvProviderKeeper: ccvProviderKeeper, ccvProviderParamSpace: ccvProviderParamSpace}
}

// Migratev1Tov2 migrates a provider from v1.0.0 to v2.0.0.
func (m Migrator) Migratev1Tov2(ctx sdk.Context) error {
	// Migrate params
	MigrateParamsv1Tov2(ctx,
		m.ccvProviderParamSpace,
		// See https://github.com/cosmos/interchain-security/blob/7861804cb311507ec6aebebbfad60ea42eb8ed4b/x/ccv/provider/keeper/params.go#L84
		// The v1.1.0-multiden version of ICS hardcodes this param as 10 of bond type: k.stakingKeeper.BondDenom(ctx).
		// Here we use the same starting value, but the param can now be changed through governance.
		sdk.NewCoin(m.ccvProviderKeeper.BondDenom(ctx), sdk.NewInt(10000000)),
	)

	// Delete select consumer genesis states for consumers that're launched
	MigrateConsumerGenesisStatesv1Tov2(ctx, m.ccvProviderKeeper)

	// Migrate keys to accommodate fix from https://github.com/cosmos/interchain-security/pull/786
	MigrateKeysv1Tov2(ctx, m.ccvProviderKeeper)

	return nil
}

// MigrateParamsv1Tov2 migrates the provider CCV module params from v1.0.0 to v2.0.0,
// setting default values for new params.
func MigrateParamsv1Tov2(ctx sdk.Context, paramsSubspace paramtypes.Subspace, consumerRewardDenomRegistrationFee sdk.Coin) {
	// Get old params
	var templateClient ibctmtypes.ClientState
	paramsSubspace.Get(ctx, providertypes.KeyTemplateClient, &templateClient)
	var trustingPeriodFraction string
	paramsSubspace.Get(ctx, providertypes.KeyTrustingPeriodFraction, &trustingPeriodFraction)
	var ccvTimeoutPeriod time.Duration
	paramsSubspace.Get(ctx, ccvtypes.KeyCCVTimeoutPeriod, &ccvTimeoutPeriod)
	var initTimeoutPeriod time.Duration
	paramsSubspace.Get(ctx, providertypes.KeyInitTimeoutPeriod, &initTimeoutPeriod)
	var vscTimeoutPeriod time.Duration
	paramsSubspace.Get(ctx, providertypes.KeyVscTimeoutPeriod, &vscTimeoutPeriod)
	var slashMeterReplenishPeriod time.Duration
	paramsSubspace.Get(ctx, providertypes.KeySlashMeterReplenishPeriod, &slashMeterReplenishPeriod)
	var slashMeterReplenishFraction string
	paramsSubspace.Get(ctx, providertypes.KeySlashMeterReplenishFraction, &slashMeterReplenishFraction)
	var maxThrottledPackets int64
	paramsSubspace.Get(ctx, providertypes.KeyMaxThrottledPackets, &maxThrottledPackets)

	// Recycle old params, set new param to input value
	newParams := providertypes.NewParams(
		&templateClient,
		trustingPeriodFraction,
		ccvTimeoutPeriod,
		initTimeoutPeriod,
		vscTimeoutPeriod,
		slashMeterReplenishPeriod,
		slashMeterReplenishFraction,
		maxThrottledPackets,
		consumerRewardDenomRegistrationFee,
	)

	// Persist new params
	paramsSubspace.SetParamSet(ctx, &newParams)
}

func MigrateConsumerGenesisStatesv1Tov2(ctx sdk.Context, providerKeeper Keeper) {
	// We could try to migrate existing ConsumerGenesisStates, but they're not needed after consumer launch.
	// Hence we delete them strategically.
	providerKeeper.DeleteConsumerGenesis(ctx, "neutron-1") // See https://github.com/neutron-org/mainnet-assets#parameters

	// TODO: determine if any other ConsumerGenesisStates need to be deleted, or actually migrated!
}

// Due to https://github.com/cosmos/interchain-security/pull/786,
// validators' slash logs are stored under the key prefix for slash acks.
// This method will extract "slash logs" from the slash acks part of the store, and put the slash logs
// in their appropriate store location.
func MigrateKeysv1Tov2(ctx sdk.Context, providerKeeper Keeper) {
	keys := providerKeeper.getAllKeysUnderSlashAcksPrefix(ctx)

	// Get valid consumer chainIDs
	consumers := providerKeeper.GetAllConsumerChains(ctx)
	consumerChainIds := make(map[string]struct{})
	for _, consumer := range consumers {
		consumerChainIds[consumer.ChainId] = struct{}{}
	}

	keysToMigrate := [][]byte{}

	// iterate through all keys under slash acks prefix
	for _, key := range keys {
		bzAfterPrefix := key[1:]
		// If bz after prefix is in consumerChainIds,
		// then this key is a valid slash acks key, no migration needed
		if _, ok := consumerChainIds[string(bzAfterPrefix)]; ok {
			continue
		}
		// Otherwise this key is potentially/hopefully a slash log key to migrate

		// Validate that after the prefix, it's just a cons address stored in the key
		if err := sdk.VerifyAddressFormat(bzAfterPrefix); err != nil {
			// We could panic here, but prob best to log corrupted key and move on.
			// This case should not happen!
			ctx.Logger().Error("unexpected key under slash acks prefix", "key", key)
			continue
		}
		keysToMigrate = append(keysToMigrate, key)
	}

	// Migrate slash logs to their correct store location
	store := ctx.KVStore(providerKeeper.storeKey)
	for _, key := range keysToMigrate {
		keyNoPrefix := key[1:]
		keyCorrectPrefix := append([]byte{providertypes.SlashLogBytePrefix}, keyNoPrefix...)
		valueBz := store.Get(key)
		store.Set(keyCorrectPrefix, valueBz)
		store.Delete(key)
	}
}

func (k Keeper) getAllKeysUnderSlashAcksPrefix(ctx sdk.Context) [][]byte {
	store := ctx.KVStore(k.storeKey)
	prefix := []byte{providertypes.SlashAcksBytePrefix}
	iterator := sdk.KVStorePrefixIterator(store, prefix)
	defer iterator.Close()
	keys := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keys = append(keys, iterator.Key()) // Values are not used for migration, just keys
	}
	return keys
}

// TODO: the following hackyness could be removed if we're able to reference older versions of ICS.
// This would likely require go.mod split, and a testing module that could depend on multiple ICS versions.

// LEGACY METHOD USED FOR TESTING MIGRATION ONLY. DO NOT USE!
// This method is copy/pasted from ICS v1.0.0.
func SlashLogKeyOnlyForTesting(providerAddr sdk.ConsAddress) []byte {
	return append([]byte{providertypes.SlashAcksBytePrefix}, providerAddr.Bytes()...)
}

// LEGACY METHOD USED FOR TESTING MIGRATION ONLY. DO NOT USE!
// This method mimics SetSlashLog from ICS v1.0.0.
func (k Keeper) SetSlashLogOnlyForTesting(
	ctx sdk.Context,
	providerAddr sdk.ConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(SlashLogKeyOnlyForTesting(providerAddr), []byte{})
}

// LEGACY METHOD USED FOR TESTING MIGRATION ONLY. DO NOT USE!
// This method mimics GetSlashLog from ICS v1.0.0.
func (k Keeper) GetSlashLogOnlyForTesting(
	ctx sdk.Context,
	providerAddr sdk.ConsAddress,
) (found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(SlashLogKeyOnlyForTesting(providerAddr))
	return bz != nil
}
