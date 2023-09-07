package keeper

import (
	"github.com/coinbase/rosetta-sdk-go/storage/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

type Migrator struct {
	ccvProviderKeeper Keeper
}

func NewMigrator(ccvProviderKeeper Keeper) Migrator {
	return Migrator{ccvProviderKeeper: ccvProviderKeeper}
}

func (m Migrator) Migrate2to3(ctx sdk.Context) error {
	return m.ccvProviderKeeper.MigrateConsumerAddrStoreKey(ctx)
}

func (k Keeper) MigrateConsumerAddrStoreKey(ctx sdk.Context) error {
	store := ctx.KVStore(k.storeKey)
	var prefixCon []byte

	prefixCon = []byte{types.ValidatorsByConsumerAddrBytePrefix}

	iteratorCon := sdk.KVStorePrefixIterator(store, prefixCon)
	defer iteratorCon.Close()
	for ; iteratorCon.Valid(); iteratorCon.Next() {
		// ParseChainIdAndConsAddrKey is used in other places, so it was not renamed to ParseChainIdAndConsAddrKeyLegacy
		chainID, consumerAddrTmp, err := types.ParseChainIdAndConsAddrKey(types.ValidatorsByConsumerAddrBytePrefix, iteratorCon.Key())
		if err != nil {
			// An error here would indicate something is very wrong,
			// store keys are assumed to be correctly serialized in SetValidatorByConsumerAddr.
			return errors.ErrParseKeyPairFailed
		}
		consumerAddr := types.NewConsumerConsAddress(consumerAddrTmp)
		providerAddr := types.NewProviderConsAddress(iteratorCon.Value())

		// bytePrefix | ConsAddress | len(chainID) | chainID
		k.SetValidatorByConsumerAddr(ctx, chainID, consumerAddr, providerAddr)

		// delete old kv
		k.DeleteValidatorByConsumerAddrLegacy(ctx, chainID, consumerAddr)

	}

	return nil
}
