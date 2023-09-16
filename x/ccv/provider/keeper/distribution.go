package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// EndBlockRD executes EndBlock logic for the Reward Distribution sub-protocol.
// Reward Distribution follows a simple model: send tokens to the ConsumerRewardsPool,
// from where they sent to the fee collector address
func (k Keeper) EndBlockRD(ctx sdk.Context) {
	// transfers all whitelisted consumer rewards to the fee collector address
	k.TransferRewardsToFeeCollector(ctx)
}

func (k Keeper) GetConsumerRewardsPoolAddressStr(ctx sdk.Context) string {
	return k.accountKeeper.GetModuleAccount(
		ctx, types.ConsumerRewardsPool).GetAddress().String()
}

func (k Keeper) SetConsumerRewardDenom(
	ctx sdk.Context,
	denom string,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ConsumerRewardDenomsKey(denom), []byte{})
}

func (k Keeper) ConsumerRewardDenomExists(
	ctx sdk.Context,
	denom string,
) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerRewardDenomsKey(denom))
	return bz != nil
}

func (k Keeper) DeleteConsumerRewardDenom(
	ctx sdk.Context,
	denom string,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerRewardDenomsKey(denom))
}

func (k Keeper) GetAllConsumerRewardDenoms(ctx sdk.Context) (consumerRewardDenoms []string) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ConsumerRewardDenomsBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		key := iterator.Key()[1:]
		consumerRewardDenoms = append(consumerRewardDenoms, string(key))
	}

	return consumerRewardDenoms
}

// TransferRewardsToFeeCollector transfers all consumer rewards to the fee collector address
func (k Keeper) TransferRewardsToFeeCollector(ctx sdk.Context) {
	// 1. Get the denom whitelist from the store
	denoms := k.GetAllConsumerRewardDenoms(ctx)

	// 2. Iterate over the whitelist
	for _, denom := range denoms {
		// 3. For each denom, retrieve the balance from the consumer rewards pool
		balance := k.bankKeeper.GetBalance(
			ctx,
			k.accountKeeper.GetModuleAccount(ctx, types.ConsumerRewardsPool).GetAddress(),
			denom,
		)

		// if the balance is not zero,
		if !balance.IsZero() {
			// 4. Transfer the balance to the fee collector address
			err := k.bankKeeper.SendCoinsFromModuleToModule(
				ctx,
				types.ConsumerRewardsPool,
				k.feeCollectorName,
				sdk.NewCoins(balance),
			)
			if err != nil {
				k.Logger(ctx).Error("cannot sent consumer rewards to fee collector:", "reward", balance.String())
			}
		}
	}
}
