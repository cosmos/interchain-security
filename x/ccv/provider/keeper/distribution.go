package keeper

import (
	"cosmossdk.io/math"
	abci "github.com/cometbft/cometbft/abci/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
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

// ProviderAllocateConsumerRewards:

// args (call by BeginBlock)
//  - totalPreviousPower int64, bondedVotes []abci.VoteInfo

// providers states:
// - whitelisted denoms
// - consumer chains
// - Pool per
// - validators per consumer

// Naive Flow
// For each consumer
// 	- get ConsumerRewardsPool
// 	- iterate over balance denoms
// 	- if denoms is whitelisted send to validators
// 		- distribute tokens by iterating over validators <- power fraction per validators is always the same

// Opti Flow
// 	For each pool get fee collected

// 	For each bondedVotes
// 		compute powerFraction
// 		For each consumer the bondVote.Val OptIn
// 			AllocateTokens of consumer.filtered pool

// total remaining

// AllocateTokens performs reward and fee distribution to all validators based
// on the F1 fee distribution specification.
func (k Keeper) AllocateTokens(ctx sdk.Context, totalPreviousPower int64, bondedVotes []abci.VoteInfo) {
	consuChains := k.GetAllConsumerChains(ctx)

	// Allocate tokens to validator for each consumer they opted in to
	for _, consu := range consuChains {

		consuFeeCollected := k.GetConsumerFeeCollected(ctx, consu.ChainId)
		if consuFeeCollected.IsZero() {
			continue
		}

		// transfer collected fees to the distribution module account
		err := k.bankKeeper.SendCoinsFromModuleToModule(
			ctx,
			k.GetConsumerModuleAccount(ctx, consu.ChainId),
			distributiontypes.ModuleName,
			consuFeeCollected,
		)
		if err != nil {
			panic(err)
		}

		feesCollected := sdk.NewDecCoinsFromCoins(consuFeeCollected...)

		// temporary workaround to keep CanWithdrawInvariant happy
		// general discussions here: https://github.com/cosmos/cosmos-sdk/issues/2906#issuecomment-441867634
		feePool := k.distributionKeeper.GetFeePool(ctx)
		if totalPreviousPower == 0 {
			feePool.CommunityPool = feePool.CommunityPool.Add(feesCollected...)
			k.distributionKeeper.SetFeePool(ctx, feePool)
			return
		}

		// calculate fraction allocated to validators
		remaining := feesCollected
		communityTax := k.distributionKeeper.GetCommunityTax(ctx)
		voteMultiplier := math.LegacyOneDec().Sub(communityTax)
		feeMultiplier := feesCollected.MulDecTruncate(voteMultiplier)

		// allocate tokens to consumer validators

		feesAllocated := k.AllocateTokensToConsumerValidators(
			ctx,
			consu.ChainId,
			totalPreviousPower,
			bondedVotes,
			feeMultiplier,
		)
		remaining = remaining.Sub(feesAllocated)

		// allocate community funding
		feePool.CommunityPool = feePool.CommunityPool.Add(remaining...)
		k.distributionKeeper.SetFeePool(ctx, feePool)
	}
}

// TODO: define which validators earned the tokens i.e. already opted in for 1000 blocks
// rename to OptIn validators?
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
		reward := fees.MulDecTruncate(powerFraction)

		k.distributionKeeper.AllocateTokensToValidator(
			ctx,
			k.stakingKeeper.ValidatorByConsAddr(ctx, valConsAddr),
			reward,
		)
		totalReward = totalReward.Add(reward...)
	}

	return
}

func (k Keeper) GetConsumerFeeCollected(ctx sdk.Context, chainID string) (feesCollected sdk.Coins) {
	// get whitelisted denoms for consumer chain
	// note that they may differ per consumer in the future
	denoms := k.GetAllConsumerRewardDenoms(ctx)

	// sum the total fees collected
	for _, denom := range denoms {
		balance := k.bankKeeper.GetBalance(
			ctx,
			k.GetConsumerModuleAccountAddress(ctx, chainID),
			denom,
		)
		feesCollected = feesCollected.Add(balance)
	}

	return
}

func (k Keeper) GetConsumerModuleAccountAddress(ctx sdk.Context, chainID string) sdk.AccAddress {
	return authtypes.NewModuleAddress(k.GetConsumerModuleAccount(ctx, chainID))
}
