package keeper

import (
	"cosmossdk.io/math"
	abci "github.com/cometbft/cometbft/abci/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// BeginBlockRD executes BeginBlock logic for the Reward Distribution sub-protocol.
func (k Keeper) BeginBlockRD(ctx sdk.Context, req abci.RequestBeginBlock) {
	// transfers all whitelisted consumer rewards to the fee collector address

	// determine the total power signing the block
	var previousTotalPower int64
	for _, voteInfo := range req.LastCommitInfo.GetVotes() {
		previousTotalPower += voteInfo.Validator.Power
	}

	// TODO this is Tendermint-dependent
	// ref https://github.com/cosmos/cosmos-sdk/issues/3095
	if ctx.BlockHeight() > 1 {
		k.AllocateTokens(ctx, previousTotalPower, req.LastCommitInfo.GetVotes())
	}
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

// AllocateTokens performs reward and fee distribution to all validators based
// on the Partial Set Security distribution specification.
func (k Keeper) AllocateTokens(ctx sdk.Context, totalPreviousPower int64, bondedVotes []abci.VoteInfo) {
	// return if there is no coins in the consumer rewards pool
	if k.GetConsumerRewardsPool(ctx).IsZero() {
		return
	}

	// Iterate over all registered consumer chains
	for _, consumer := range k.GetAllConsumerChains(ctx) {

		// transfer the consumer rewards to the distribution module account
		// note that the rewards transferred are only consumer whitelisted denoms
		rewardsCollected, err := k.TransferConsumerRewardsToDistributionModule(ctx, consumer.ChainId)
		if err != nil {
			panic(err)
		}

		if rewardsCollected.IsZero() {
			continue
		}

		rewardsCollectedDec := sdk.NewDecCoinsFromCoins(rewardsCollected...)

		// temporary workaround to keep CanWithdrawInvariant happy
		// general discussions here: https://github.com/cosmos/cosmos-sdk/issues/2906#issuecomment-441867634
		feePool := k.distributionKeeper.GetFeePool(ctx)
		if totalPreviousPower == 0 {
			feePool.CommunityPool = feePool.CommunityPool.Add(rewardsCollectedDec...)
			k.distributionKeeper.SetFeePool(ctx, feePool)
			return
		}

		// Calculate the reward allocations
		remaining := rewardsCollectedDec
		communityTax := k.distributionKeeper.GetCommunityTax(ctx)
		voteMultiplier := math.LegacyOneDec().Sub(communityTax)
		feeMultiplier := rewardsCollectedDec.MulDecTruncate(voteMultiplier)

		// allocate tokens to consumer validators
		feeAllocated := k.AllocateTokensToConsumerValidators(
			ctx,
			consumer.ChainId,
			totalPreviousPower,
			bondedVotes,
			feeMultiplier,
		)
		remaining = remaining.Sub(feeAllocated)

		// allocate community funding
		feePool.CommunityPool = feePool.CommunityPool.Add(remaining...)
		k.distributionKeeper.SetFeePool(ctx, feePool)
	}
}

// TODO: define which validators earned the tokens, i.e. already opted in for 1000 blocks
func (k Keeper) AllocateTokensToConsumerValidators(
	ctx sdk.Context,
	chainID string,
	totalPreviousPower int64,
	bondedVotes []abci.VoteInfo,
	fees sdk.DecCoins,
) (totalReward sdk.DecCoins) {
	for _, vote := range bondedVotes {
		valConsAddr := vote.Validator.Address

		if _, found := k.GetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(valConsAddr)); !found {
			continue
		}
		// TODO: Consider micro-slashing for missing votes.
		//
		// Ref: https://github.com/cosmos/cosmos-sdk/issues/2525#issuecomment-430838701
		powerFraction := math.LegacyNewDec(vote.Validator.Power).QuoTruncate(math.LegacyNewDec(totalPreviousPower))
		feeFraction := fees.MulDecTruncate(powerFraction)

		k.distributionKeeper.AllocateTokensToValidator(
			ctx,
			k.stakingKeeper.ValidatorByConsAddr(ctx, valConsAddr),
			feeFraction,
		)
		totalReward = totalReward.Add(feeFraction...)
	}

	return
}

// TransferConsumerRewardsToDistributionModule transfers the collected rewards of the given consumer chain
// from the consumer rewards pool module account to a the distribution module
func (k Keeper) TransferConsumerRewardsToDistributionModule(
	ctx sdk.Context,
	chainID string,
) (sdk.Coins, error) {

	// Get coins of the consumer reward pool
	pool := k.GetConsumerRewardsAllocation(ctx, chainID)

	// Truncate coin rewards
	rewards, _ := pool.Rewards.TruncateDecimal()

	// Extract the whitelisted denoms
	coinsToSend := sdk.Coins{}
	denoms := k.GetAllConsumerRewardDenoms(ctx)
	for _, denom := range denoms {
		if found, coin := rewards.Find(denom); found {
			coinsToSend = coinsToSend.Add(coin)
		}
	}

	// NOTE the consumer isn't a module account, however its coins
	// are held in the consumer reward pool module account. Thus the reward
	// must be reduced separately from the SendCoinsFromModuleToAccount call
	remainingDec, negative := pool.Rewards.SafeSub(sdk.NewDecCoinsFromCoins(coinsToSend...))
	if negative {
		return sdk.Coins{}, distrtypes.ErrBadDistribution
	}

	// Update consumer reward pool with the remaining decimal coins
	pool.Rewards = remainingDec

	// Send coins to distribution module account
	err := k.bankKeeper.SendCoinsFromModuleToModule(ctx, types.ConsumerRewardsPool, distrtypes.ModuleName, coinsToSend)
	if err != nil {
		return sdk.Coins{}, err
	}

	k.SetConsumerRewardsAllocation(ctx, chainID, pool)
	return coinsToSend, nil
}

// consumer reward pools getter and setter

// get the consumer reward pool distribution info
func (k Keeper) GetConsumerRewardsAllocation(ctx sdk.Context, chainID string) (pool types.ConsumerRewardsAllocation) {
	store := ctx.KVStore(k.storeKey)
	b := store.Get(types.ConsumerRewardPoolKey(chainID))
	k.cdc.MustUnmarshal(b, &pool)
	return
}

// set the consumer reward pool distribution info
func (k Keeper) SetConsumerRewardsAllocation(ctx sdk.Context, chainID string, pool types.ConsumerRewardsAllocation) {
	store := ctx.KVStore(k.storeKey)
	b := k.cdc.MustMarshal(&pool)
	store.Set(types.ConsumerRewardPoolKey(chainID), b)
}

// GetConsumerRewardsPool returns the balance
// of the consumer rewards pool module account
func (k Keeper) GetConsumerRewardsPool(ctx sdk.Context) sdk.Coins {
	return k.bankKeeper.GetAllBalances(
		ctx,
		k.accountKeeper.GetModuleAccount(ctx, types.ConsumerRewardsPool).GetAddress(),
	)
}
