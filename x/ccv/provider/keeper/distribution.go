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

// AllocateTokens performs rewards distribution to the community pool and validators
// based on the Partial Set Security distribution specification.
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
			k.Logger(ctx).Error(
				"fail to transfer rewards to distribution module for chain %s: %s",
				consumer.ChainId,
				err,
			)
			continue
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
			bondedVotes,
			feeMultiplier,
		)
		remaining = remaining.Sub(feeAllocated)

		// allocate community funding
		feePool.CommunityPool = feePool.CommunityPool.Add(remaining...)
		k.distributionKeeper.SetFeePool(ctx, feePool)
	}
}

// TODO: allocate tokens to validators that opted-in and for long enough e.g. 1000 blocks
// once the opt-in logic is integrated QueueVSCPackets()
//
// AllocateTokensToConsumerValidators allocates the given tokens from the
// from consumer rewards pool to validator according to their voting power
func (k Keeper) AllocateTokensToConsumerValidators(
	ctx sdk.Context,
	chainID string,
	bondedVotes []abci.VoteInfo,
	tokens sdk.DecCoins,
) (totalReward sdk.DecCoins) {
	// return early if the tokens are empty
	if tokens.Empty() {
		return totalReward
	}

	// get the consumer total voting power from the votes
	totalPower := k.ComputeConsumerTotalVotingPower(ctx, chainID, bondedVotes)
	if totalPower == 0 {
		return totalReward
	}

	for _, vote := range bondedVotes {
		// TODO: should check if validator IsOptIn or continue here
		consAddr := sdk.ConsAddress(vote.Validator.Address)

		powerFraction := math.LegacyNewDec(vote.Validator.Power).QuoTruncate(math.LegacyNewDec(totalPower))
		tokensFraction := tokens.MulDecTruncate(powerFraction)

		k.distributionKeeper.AllocateTokensToValidator(
			ctx,
			k.stakingKeeper.ValidatorByConsAddr(ctx, consAddr),
			tokensFraction,
		)
		totalReward = totalReward.Add(tokensFraction...)
	}

	return totalReward
}

// TransferConsumerRewardsToDistributionModule transfers the collected rewards of the given consumer chain
// from the consumer rewards pool module account to a the distribution module
func (k Keeper) TransferConsumerRewardsToDistributionModule(
	ctx sdk.Context,
	chainID string,
) (sdk.Coins, error) {
	// Get coins of the consumer rewards allocation
	allocation := k.GetConsumerRewardsAllocation(ctx, chainID)

	if allocation.Rewards.IsZero() {
		return sdk.Coins{}, nil
	}

	// Truncate coin rewards
	rewardsToSend, _ := allocation.Rewards.TruncateDecimal()

	// NOTE the consumer rewards allocation isn't a module account, however its coins
	// are held in the consumer reward pool module account. Thus the consumer
	// rewards allocation must be reduced separately from the SendCoinsFromModuleToAccount call.

	// Update consumer rewards allocation with the remaining decimal coins
	allocation.Rewards = allocation.Rewards.Sub(sdk.NewDecCoinsFromCoins(rewardsToSend...))

	// Send coins to distribution module account
	err := k.bankKeeper.SendCoinsFromModuleToModule(ctx, types.ConsumerRewardsPool, distrtypes.ModuleName, rewardsToSend)
	if err != nil {
		return sdk.Coins{}, err
	}

	k.SetConsumerRewardsAllocation(ctx, chainID, allocation)
	return rewardsToSend, nil
}

// consumer reward pools getter and setter

// GetConsumerRewardsAllocation the onsumer rewards allocation for the given chain ID
func (k Keeper) GetConsumerRewardsAllocation(ctx sdk.Context, chainID string) (pool types.ConsumerRewardsAllocation) {
	store := ctx.KVStore(k.storeKey)
	b := store.Get(types.ConsumerRewardsAllocationKey(chainID))
	k.cdc.MustUnmarshal(b, &pool)
	return
}

// SetConsumerRewardsAllocation sets the consumer rewards allocation for the given chain ID
func (k Keeper) SetConsumerRewardsAllocation(ctx sdk.Context, chainID string, pool types.ConsumerRewardsAllocation) {
	store := ctx.KVStore(k.storeKey)
	b := k.cdc.MustMarshal(&pool)
	store.Set(types.ConsumerRewardsAllocationKey(chainID), b)
}

// GetConsumerRewardsPool returns the balance
// of the consumer rewards pool module account
func (k Keeper) GetConsumerRewardsPool(ctx sdk.Context) sdk.Coins {
	return k.bankKeeper.GetAllBalances(
		ctx,
		k.accountKeeper.GetModuleAccount(ctx, types.ConsumerRewardsPool).GetAddress(),
	)
}

// ComputeConsumerTotalVotingPower returns the total voting power for a given consumer chain
// by summing its opted-in validators votes
func (k Keeper) ComputeConsumerTotalVotingPower(ctx sdk.Context, chainID string, votes []abci.VoteInfo) int64 {
	// TODO: create a optedIn set from the OptedIn validators
	// and sum their validator power

	var totalPower int64

	// sum the opted-in validators set voting powers
	for _, vote := range votes {
		// TODO: check that val is in the optedIn set

		totalPower += vote.Validator.Power
	}

	return totalPower
}
