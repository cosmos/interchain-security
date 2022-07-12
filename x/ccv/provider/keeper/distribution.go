package keeper

import (
	"errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

func (k Keeper) GetFeeCollectorAddressStr(ctx sdk.Context) string {
	return k.accountKeeper.GetModuleAccount(
		ctx, k.feeCollectorName).GetAddress().String()
}

func (k Keeper) GetProviderDistributionAddressStr(ctx sdk.Context) string {
	return k.accountKeeper.GetModuleAccount(
		ctx, types.DistributionAccount).GetAddress().String()
}

func (k Keeper) HandleProviderPoolWeights(ctx sdk.Context, weights ccv.ProviderPoolWeights) error {
	if weights.GetTokens().IsZero() {
		return errors.New("Tokens should not be zero ")
	}
	if len(weights.Addresses) == 0 {
		return errors.New("Addresses should not be empty ")
	}
	if len(weights.Addresses) != len(weights.Weights) {
		return errors.New("Addresses size does not equal to weights size ")
	}
	totalWeights := sdk.ZeroInt()
	for _, weight := range weights.Weights {
		totalWeights = totalWeights.Add(weight)
	}
	if !totalWeights.Equal(weights.TotalWeight) {
		return errors.New("TotalWeight does not equal to the sum of weights")
	}

	k.AddPendingProviderPoolWeights(ctx, &weights)
	return nil
}

func (k Keeper) Distribute(ctx sdk.Context) {
	address := k.accountKeeper.GetModuleAccount(
		ctx, types.DistributionAccount).GetAddress()
	balances := k.bankKeeper.GetAllBalances(ctx, address)
	if balances.IsZero() {
		return
	}

	pending := k.GetPendingProviderPoolWeights(ctx)
	breakIndex := -1
	for i, ppw := range pending.GetPoolWeights() {
		if balances.Len() == 0 || ppw.Tokens.IsAnyGT(balances) {
			breakIndex = i
			break
		}
		// transfer all tokens to distribution module address
		if err := k.bankKeeper.SendCoinsFromModuleToModule(ctx, types.DistributionAccount, k.distributionName, ppw.GetTokens()); err != nil {
			panic(err)
		}
		balances = balances.Sub(ppw.Tokens)
		k.AllocateTokens(ctx, *ppw)
	}

	if breakIndex == 0 { // no pending ppw can be handled
		return
	}
	if breakIndex == -1 { // all pending ppw can be handled
		k.SetPendingProviderPoolWeights(ctx, ccv.PendingPPWs{})
		return
	}
	pending.PoolWeights = pending.PoolWeights[breakIndex:]
	k.SetPendingProviderPoolWeights(ctx, pending)
}

func (k Keeper) AllocateTokens(ctx sdk.Context, weights ccv.ProviderPoolWeights) {
	excess := sdk.NewCoins()
	remaining := weights.GetTokens()
	for i := range weights.Addresses {
		valRewards := sdk.NewDecCoinsFromCoins(weights.GetTokens()...).
			MulDec(sdk.NewDecFromBigInt(weights.Weights[i].BigInt())).
			QuoDec(sdk.NewDecFromBigInt(weights.TotalWeight.BigInt()))
		truncatedValRewards, _ := valRewards.TruncateDecimal()
		remaining = remaining.Sub(truncatedValRewards)

		val, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, weights.Addresses[i])
		if !found {
			excess = excess.Add(truncatedValRewards...)
			continue
		}
		k.distributionKeeper.AllocateTokensToValidator(ctx, val, sdk.NewDecCoinsFromCoins(truncatedValRewards...))
	}

	// add excess tokens to DistributionExcessPool
	excess = excess.Add(remaining...)
	distributionExcessPool := k.GetDistributionExcessPool(ctx)
	if distributionExcessPool.Excess == nil {
		distributionExcessPool.Excess = sdk.NewCoins()
	}
	distributionExcessPool.Excess = distributionExcessPool.Excess.Add(excess...)
	k.SetDistributionExcessPool(ctx, distributionExcessPool)
}

func (k Keeper) SetDistributionExcessPool(ctx sdk.Context, excess types.DistributionExcessPool) {
	store := ctx.KVStore(k.storeKey)
	b := k.cdc.MustMarshal(&excess)
	store.Set(types.DistributionExcessKey, b)
}

func (k Keeper) GetDistributionExcessPool(ctx sdk.Context) (excess types.DistributionExcessPool) {
	store := ctx.KVStore(k.storeKey)
	b := store.Get(types.DistributionExcessKey)
	if b != nil {
		k.cdc.MustUnmarshal(b, &excess)
	}
	return
}

func (k Keeper) SetPendingProviderPoolWeights(ctx sdk.Context, pendingPPWs ccv.PendingPPWs) {
	store := ctx.KVStore(k.storeKey)
	b := k.cdc.MustMarshal(&pendingPPWs)
	store.Set(types.PendingProviderPoolWeightsKey, b)
}

func (k Keeper) GetPendingProviderPoolWeights(ctx sdk.Context) (pendingPPWs ccv.PendingPPWs) {
	store := ctx.KVStore(k.storeKey)
	b := store.Get(types.PendingProviderPoolWeightsKey)
	if b != nil {
		k.cdc.MustUnmarshal(b, &pendingPPWs)
	}
	return
}

func (k Keeper) AddPendingProviderPoolWeights(ctx sdk.Context, weights *ccv.ProviderPoolWeights) {
	pending := k.GetPendingProviderPoolWeights(ctx)
	if pending.GetPoolWeights() == nil {
		pending.PoolWeights = make([]*ccv.ProviderPoolWeights, 0)
	}
	pending.PoolWeights = append(pending.PoolWeights, weights)
	k.SetPendingProviderPoolWeights(ctx, pending)
}
