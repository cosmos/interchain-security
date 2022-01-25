

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/x/ccv/child/types"

	// XXX delete or uncomment this block before merge
	//ibctypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
)

// Simple model, donate tokens to the fee pool of the provider validator set
// reference: cosmos/ibc-go/modules/apps/transfer/keeper/msg_server.go
func (k Keeper) DonateToProviderValidatorSet(ctx sdk.Context) {
	if !k.shouldTransmit(ctx) {
		return
	}

	srcPort := 0    // ???
	srcChannel := 0 // ???

	// work around to reuse the IBC token transfer logic
	consumerFeePoolAddr := k.accountKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
	providerFeePoolAddrStr := k.accountKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()

	tokens := k.bankKeeper.GetAllBalances(ctx, consumerFeePoolAddr.GetAddress())
	for _, token := range tokens {

		// XXX delete or uncomment this block before merge
		//if !strings.HasPrefix(token.Denom, "ibc/") {
		//    denomTrace := ibctypes.ParseDenomTrace(token.Denom)
		//    token.Denom = denomTrace.IBCDenom()
		//}

		timeoutHeight := 0
		timeoutTimestamp := 0

		return k.ibcKeeper.SendTransfer(ctx,
			srcPort,
			srcChannel,
			token,
			consumerFeePoolAcc.String(),
			providerFeePoolAcc.String(),
			timeoutHeight,
			timeoutTimestamp,
		)
	}
}

// -----------------------------------------------------------
// XXX rewrite comment
// Return a validator-allocation function where the tokens are allocated
// to is intended to be used in conjunction with IBC
// to pass rewards on to a provider chain.
func (k Keeper) AllocateTokensToProviderValidatorHoldingPool(
	ctx sdk.Context, val stakingtypes.ValidatorI, tokens sdk.DecCoins) {

	key := types.DistributionValidatorHoldingPoolKey(val.GetOperator())
	store := ctx.KVStore(k.storeKey)

	// add tokens to the validator pool
	// or create one if it doesn't exist
	valPool := &ProviderValidatorHoldingPool{}
	if store.Has(key) {
		poolBz := store.Get(key)
		err := valPool.Unmarshal(poolBz)
		if err != nil {
			panic(fmt.Sprintf("error unmarshalling ProviderValidatorHoldingPool: %v", err))
		}
		valPool.Pool = valPool.Pool.Add(tokens)
	} else {
		valPool = &ProviderValidatorHoldingPool{
			// XXX  XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX XXX
			Pool: tokens,
		}
	}
	updatedPoolBz, err := valPool.Marshal(poolBz)
	if err != nil {
		panic(fmt.Sprintf("error marshalling ProviderValidatorHoldingPool: %v", err))
	}
	store.Set(key, updatedPoolBz)
}

func (k Keeper) TransmitHoldingsToProvider(ctx sdk.Context) {
	if !k.shouldTransmit(ctx) {
		return
	}

	// iterate the store and add all entries to a provider
	// pool for transmission
	pp := &ProviderPool{}
	store := ctx.KVStore(k.storeKey)

	iter := sdk.KVStorePrefixIterator(store, types.DistributionValidatorHoldingPoolKeyPrefix)
	defer iter.Close()

	for ; iter.Valid(); iter.Next() {
		bz := iter.Value()
		valPool := &ProviderValidatorHoldingPool{}
		err := valPool.Unmarshal(bz)
		if err != nil {
			panic(fmt.Sprintf("error unmarshalling ProviderValidatorHoldingPool: %v", err))
		}
		pp.Entries = append(pp.Entries, valPool)
	}

	// XXX IBC transmission

}

// test to see if enough blocks have passed for
// a transmission to occur
func (k Keeper) shouldTransmit(ctx sdk.Context) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(LastDistributionTransmissionKey)
	if bz == nil {
		return true
	}
	ltbh := &LastTransmissionBlockHeight{}
	ltbh.Unmarshal(bz)
	bpdt := k.GetBlocksPerDistributionTransmission(ctx)
	curHeight := ctx.BlockHeight()
	return (curHeight - ltbh) >= bpdt
}
