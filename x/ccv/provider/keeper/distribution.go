package keeper

import (
	"context"

	storetypes "cosmossdk.io/store/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// BeginBlockRD executes BeginBlock logic for the Reward Distribution sub-protocol.
func (k Keeper) BeginBlockRD(ctx sdk.Context) {
	// TODO this is Tendermint-dependent
	// ref https://github.com/cosmos/cosmos-sdk/issues/3095
	if ctx.BlockHeight() > 1 {
		k.AllocateTokens(ctx)
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
	iterator := storetypes.KVStorePrefixIterator(store, []byte{types.ConsumerRewardDenomsBytePrefix})
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		key := iterator.Key()[1:]
		consumerRewardDenoms = append(consumerRewardDenoms, string(key))
	}

	return consumerRewardDenoms
}

// AllocateTokens performs rewards distribution to the community pool and validators
// based on the Partial Set Security distribution specification.
func (k Keeper) AllocateTokens(ctx sdk.Context) {
	// return if there is no coins in the consumer rewards pool
	if k.GetConsumerRewardsPool(ctx).IsZero() {
		return
	}

	// Iterate over all registered consumer chains
	for _, consumerChainID := range k.GetAllRegisteredConsumerChainIDs(ctx) {

		// note that it's possible that no rewards are collected even though the
		// reward pool isn't empty. This can happen if the reward pool holds some tokens
		// of non-whitelisted denominations.
		alloc := k.GetConsumerRewardsAllocation(ctx, consumerChainID)
		if alloc.Rewards.IsZero() {
			continue
		}

		// temporary workaround to keep CanWithdrawInvariant happy
		// general discussions here: https://github.com/cosmos/cosmos-sdk/issues/2906#issuecomment-441867634
		if k.ComputeConsumerTotalVotingPower(ctx, consumerChainID) == 0 {
			rewardsToSend, rewardsChange := alloc.Rewards.TruncateDecimal()
			err := k.distributionKeeper.FundCommunityPool(context.Context(ctx), rewardsToSend, k.accountKeeper.GetModuleAccount(ctx, types.ConsumerRewardsPool).GetAddress())
			if err != nil {
				k.Logger(ctx).Error(
					"fail to allocate rewards from consumer chain %s to community pool: %s",
					consumerChainID,
					err,
				)
			}

			// set the consumer allocation to the remaining reward decimals
			alloc.Rewards = rewardsChange
			k.SetConsumerRewardsAllocation(ctx, consumerChainID, alloc)

			return
		}

		// Consumer rewards are distributed between the validators and the community pool.
		// The decimals resulting from the distribution are expected to remain in the consumer reward allocations.

		communityTax, err := k.distributionKeeper.GetCommunityTax(ctx)
		if err != nil {
			k.Logger(ctx).Error(
				"cannot get community tax while allocating rewards from consumer chain %s: %s",
				consumerChainID,
				err,
			)
			continue
		}

		// compute rewards for validators
		consumerRewards := alloc.Rewards
		voteMultiplier := math.LegacyOneDec().Sub(communityTax)
		validatorsRewards := consumerRewards.MulDecTruncate(voteMultiplier)

		// compute remaining rewards for the community pool
		remaining := consumerRewards.Sub(validatorsRewards)

		// transfer validators rewards to distribution module account
		validatorsRewardsTrunc, validatorsRewardsChange := validatorsRewards.TruncateDecimal()
		err = k.bankKeeper.SendCoinsFromModuleToModule(ctx, types.ConsumerRewardsPool, distrtypes.ModuleName, validatorsRewardsTrunc)
		if err != nil {
			k.Logger(ctx).Error(
				"cannot send rewards to distribution module account %s: %s",
				consumerChainID,
				err,
			)
			continue
		}

		// allocate tokens to consumer validators
		k.AllocateTokensToConsumerValidators(
			ctx,
			consumerChainID,
			sdk.NewDecCoinsFromCoins(validatorsRewardsTrunc...),
		)

		// allocate remaining rewards to the community pool
		remainingRewards, remainingChanges := remaining.TruncateDecimal()
		err = k.distributionKeeper.FundCommunityPool(context.Context(ctx), remainingRewards, k.accountKeeper.GetModuleAccount(ctx, types.ConsumerRewardsPool).GetAddress())
		if err != nil {
			k.Logger(ctx).Error(
				"fail to allocate rewards from consumer chain %s to community pool: %s",
				consumerChainID,
				err,
			)
			continue
		}

		// set consumer allocations to the remaining rewards decimals
		alloc.Rewards = validatorsRewardsChange.Add(remainingChanges...)
		k.SetConsumerRewardsAllocation(ctx, consumerChainID, alloc)
	}
}

// IsEligibleForConsumerRewards returns `true` if the validator with `consumerValidatorHeight` has been a consumer
// validator for a long period of time and hence is eligible to receive rewards, and false otherwise
func (k Keeper) IsEligibleForConsumerRewards(ctx sdk.Context, consumerValidatorHeight int64) bool {
	numberOfBlocksToStartReceivingRewards := k.GetNumberOfEpochsToStartReceivingRewards(ctx) * k.GetBlocksPerEpoch(ctx)

	// a validator is eligible for rewards if it has been a consumer validator for `NumberOfEpochsToStartReceivingRewards` epochs
	return (ctx.BlockHeight() - consumerValidatorHeight) >= numberOfBlocksToStartReceivingRewards
}

// AllocateTokensToConsumerValidators allocates tokens
// to the given consumer chain's validator set
func (k Keeper) AllocateTokensToConsumerValidators(
	ctx sdk.Context,
	chainID string,
	tokens sdk.DecCoins,
) (allocated sdk.DecCoins) {
	// return early if the tokens are empty
	if tokens.Empty() {
		return allocated
	}

	// get the total voting power of the consumer valset
	totalPower := math.LegacyNewDec(k.ComputeConsumerTotalVotingPower(ctx, chainID))
	if totalPower.IsZero() {
		return allocated
	}

	// Allocate tokens by iterating over the consumer validators
	for _, consumerVal := range k.GetConsumerValSet(ctx, chainID) {
		// if a validator is not eligible, this means that the other eligible validators would get more rewards
		if !k.IsEligibleForConsumerRewards(ctx, consumerVal.JoinHeight) {
			continue
		}

		consAddr := sdk.ConsAddress(consumerVal.ProviderConsAddr)

		// get the validator tokens fraction using its voting power
		powerFraction := math.LegacyNewDec(consumerVal.Power).QuoTruncate(totalPower)
		tokensFraction := tokens.MulDecTruncate(powerFraction)

		// get the validator type struct for the consensus address
		val, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, consAddr)
		if err != nil {
			k.Logger(ctx).Error(
				"cannot find validator by consensus address",
				consAddr,
				"while allocating rewards from consumer chain",
				chainID,
				"error",
				err,
			)
			continue
		}

		// check if the validator set a custom commission rate for the consumer chain
		if cr, found := k.GetConsumerCommissionRate(ctx, chainID, types.NewProviderConsAddress(consAddr)); found {
			// set the validator commission rate
			val.Commission.CommissionRates.Rate = cr
		}

		// allocate the consumer reward tokens to the validator
		err = k.distributionKeeper.AllocateTokensToValidator(
			ctx,
			val,
			tokensFraction,
		)
		if err != nil {
			k.Logger(ctx).Error("fail to allocate tokens to validator :%s while allocating rewards from consumer chain: %s",
				consAddr, chainID)
			continue
		}

		// sum the tokens allocated
		allocated = allocated.Add(tokensFraction...)
	}

	return allocated
}

// consumer reward pools getter and setter

// GetConsumerRewardsAllocation returns the consumer rewards allocation for the given chain ID
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

// ComputeConsumerTotalVotingPower returns the validator set total voting power
// for the given consumer chain
func (k Keeper) ComputeConsumerTotalVotingPower(ctx sdk.Context, chainID string) (totalPower int64) {
	// sum the consumer validators set voting powers
	for _, v := range k.GetConsumerValSet(ctx, chainID) {

		// only consider the voting power of a validator that would receive rewards (i.e., validator has been validating for a number of blocks)
		if !k.IsEligibleForConsumerRewards(ctx, v.JoinHeight) {
			continue
		}

		totalPower += v.Power
	}

	return
}

// IdentifyConsumerChainIDFromIBCPacket checks if the packet destination matches a registered consumer chain.
// If so, it returns the consumer chain ID, otherwise an error.
func (k Keeper) IdentifyConsumerChainIDFromIBCPacket(ctx sdk.Context, packet channeltypes.Packet) (string, error) {
	channel, ok := k.channelKeeper.GetChannel(ctx, packet.DestinationPort, packet.DestinationChannel)
	if !ok {
		return "", errorsmod.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for channel ID: %s", packet.DestinationChannel)
	}
	if len(channel.ConnectionHops) != 1 {
		return "", errorsmod.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to consumer chain")
	}
	connectionID := channel.ConnectionHops[0]
	_, tmClient, err := k.getUnderlyingClient(ctx, connectionID)
	if err != nil {
		return "", err
	}

	chainID := tmClient.ChainId
	if _, ok := k.GetChainToChannel(ctx, chainID); !ok {
		return "", errorsmod.Wrapf(types.ErrUnknownConsumerChannelId, "no CCV channel found for chain with ID: %s", chainID)
	}

	return chainID, nil
}

// HandleSetConsumerCommissionRate sets a per-consumer chain commission rate for the given provider address
// on the condition that the given consumer chain exists.
func (k Keeper) HandleSetConsumerCommissionRate(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress, commissionRate math.LegacyDec) error {
	// check that the consumer chain exists
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"unknown consumer chain, with id: %s", chainID)
	}

	// validate against the minimum commission rate
	minRate, err := k.stakingKeeper.MinCommissionRate(ctx)
	if err != nil {
		return err
	}
	if commissionRate.LT(minRate) {
		return errorsmod.Wrapf(
			stakingtypes.ErrCommissionLTMinRate,
			"commission rate cannot be less than %s", minRate,
		)
	}
	// set per-consumer chain commission rate for the validator address
	return k.SetConsumerCommissionRate(
		ctx,
		chainID,
		providerAddr,
		commissionRate,
	)
}
