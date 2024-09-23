package keeper

import (
	"context"

	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
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
	iterator := storetypes.KVStorePrefixIterator(store, types.ConsumerRewardDenomsKeyPrefix())
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		key := iterator.Key()[1:]
		consumerRewardDenoms = append(consumerRewardDenoms, string(key))
	}

	return consumerRewardDenoms
}

// AllocateConsumerRewards allocates the given rewards to provider consumer chain with the given consumer id.
// The allocation respects the provider's community tax, validators fees, etc. and the remaining awards are sent
// to the community pool.
func (k Keeper) AllocateConsumerRewards(ctx sdk.Context, consumerId string, rewards sdk.DecCoins) (sdk.DecCoins, error) {
	if rewards.IsZero() {
		return sdk.DecCoins{}, nil
	}

	// temporary workaround to keep CanWithdrawInvariant happy
	// general discussions here: https://github.com/cosmos/cosmos-sdk/issues/2906#issuecomment-441867634
	if k.ComputeConsumerTotalVotingPower(ctx, consumerId) == 0 {
		rewardsToSend, rewardsChange := rewards.TruncateDecimal()
		err := k.distributionKeeper.FundCommunityPool(context.Context(ctx), rewardsToSend, k.accountKeeper.GetModuleAccount(ctx, types.ConsumerRewardsPool).GetAddress())
		if err != nil {
			k.Logger(ctx).Error(
				"fail to allocate rewards from consumer chain %s to community pool: %s",
				consumerId,
				err,
			)
		}

		// set the consumer allocation to the remaining reward decimals
		return rewardsChange, nil
	}

	// Consumer rewards are distributed between the validators and the community pool.
	// The decimals resulting from the distribution are expected to remain in the consumer reward allocations.

	communityTax, err := k.distributionKeeper.GetCommunityTax(ctx)
	if err != nil {
		k.Logger(ctx).Error(
			"cannot get community tax while allocating rewards from consumer chain %s: %s",
			consumerId,
			err,
		)
		return sdk.DecCoins{}, err
	}

	// compute rewards for validators
	consumerRewards := rewards
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
			consumerId,
			err,
		)
		return sdk.DecCoins{}, err
	}

	// allocate tokens to consumer validators
	k.AllocateTokensToConsumerValidators(
		ctx,
		consumerId,
		sdk.NewDecCoinsFromCoins(validatorsRewardsTrunc...),
	)

	// allocate remaining rewards to the community pool
	remainingRewards, remainingChanges := remaining.TruncateDecimal()
	err = k.distributionKeeper.FundCommunityPool(context.Context(ctx), remainingRewards, k.accountKeeper.GetModuleAccount(ctx, types.ConsumerRewardsPool).GetAddress())
	if err != nil {
		k.Logger(ctx).Error(
			"fail to allocate rewards from consumer chain %s to community pool: %s",
			consumerId,
			err,
		)
		return sdk.DecCoins{}, err
	}

	// set consumer allocations to the remaining rewards decimals
	return validatorsRewardsChange.Add(remainingChanges...), nil
}

// AllocateTokens performs rewards distribution to the community pool and validators
// based on the Partial Set Security distribution specification.
func (k Keeper) AllocateTokens(ctx sdk.Context) {
	// return if there is no coins in the consumer rewards pool
	if k.GetConsumerRewardsPool(ctx).IsZero() {
		return
	}

	// To avoid large iterations over all the consumer IDs, iterate only over launched consumer chains (i.e., chains
	// that have an IBC client created).
	for _, consumerId := range k.GetAllConsumersWithIBCClients(ctx) {
		oldRewards := k.GetConsumerRewardsAllocation(ctx, consumerId)
		returnedRewards, err := k.AllocateConsumerRewards(ctx, consumerId, oldRewards.Rewards)
		if err != nil {
			k.Logger(ctx).Error(
				"fail to allocate rewards for consumer chain",
				"consumer id", consumerId,
				"error", err.Error(),
			)
		} else {
			k.SetConsumerRewardsAllocation(ctx, consumerId, types.ConsumerRewardsAllocation{Rewards: returnedRewards})
		}

		allAllowlistedDenoms := append(k.GetAllConsumerRewardDenoms(ctx), k.GetAllowlistedRewardDenoms(ctx, consumerId)...)
		for _, denom := range allAllowlistedDenoms {
			cachedCtx, writeCache := ctx.CacheContext()
			consumerRewards := k.GetConsumerRewardsAllocationByDenom(cachedCtx, consumerId, denom)
			allocatedRewards, err := k.AllocateConsumerRewards(cachedCtx, consumerId, consumerRewards.Rewards)
			if err != nil {
				k.Logger(ctx).Error(
					"fail to allocate rewards for consumer chain",
					"consumer id", consumerId,
					"error", err.Error(),
				)
				continue
			}
			k.SetConsumerRewardsAllocationByDenom(cachedCtx, consumerId, denom, types.ConsumerRewardsAllocation{Rewards: allocatedRewards})
			writeCache()
		}
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
	consumerId string,
	tokens sdk.DecCoins,
) (allocated sdk.DecCoins) {
	// return early if the tokens are empty
	if tokens.Empty() {
		return allocated
	}

	// get the total voting power of the consumer valset
	totalPower := math.LegacyNewDec(k.ComputeConsumerTotalVotingPower(ctx, consumerId))
	if totalPower.IsZero() {
		return allocated
	}

	// Allocate tokens by iterating over the consumer validators
	consumerVals, err := k.GetConsumerValSet(ctx, consumerId)
	if err != nil {
		k.Logger(ctx).Error(
			"cannot get consumer validator set while allocating rewards from consumer chain",
			consumerId,
			"error",
			err,
		)
		return allocated
	}
	for _, consumerVal := range consumerVals {
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
				consumerId,
				"error",
				err,
			)
			continue
		}

		// check if the validator set a custom commission rate for the consumer chain
		if cr, found := k.GetConsumerCommissionRate(ctx, consumerId, types.NewProviderConsAddress(consAddr)); found {
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
				consAddr, consumerId)
			continue
		}

		// sum the tokens allocated
		allocated = allocated.Add(tokensFraction...)
	}

	return allocated
}

// consumer reward pools getter and setter

// GetConsumerRewardsAllocation returns the consumer rewards allocation for the given consumer id
func (k Keeper) GetConsumerRewardsAllocation(ctx sdk.Context, consumerId string) (pool types.ConsumerRewardsAllocation) {
	store := ctx.KVStore(k.storeKey)
	b := store.Get(types.ConsumerRewardsAllocationKey(consumerId))
	k.cdc.MustUnmarshal(b, &pool)
	return
}

// SetConsumerRewardsAllocation sets the consumer rewards allocation for the given consumer id
func (k Keeper) SetConsumerRewardsAllocation(ctx sdk.Context, consumerId string, pool types.ConsumerRewardsAllocation) {
	store := ctx.KVStore(k.storeKey)
	b := k.cdc.MustMarshal(&pool)
	store.Set(types.ConsumerRewardsAllocationKey(consumerId), b)
}

// DeleteConsumerRewardsAllocation deletes the consumer rewards allocation for the given consumer id
func (k Keeper) DeleteConsumerRewardsAllocation(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerRewardsAllocationKey(consumerId))
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
func (k Keeper) ComputeConsumerTotalVotingPower(ctx sdk.Context, consumerId string) (totalPower int64) {
	// sum the consumer validators set voting powers
	vals, err := k.GetConsumerValSet(ctx, consumerId)
	if err != nil {
		k.Logger(ctx).Error(
			"cannot get consumer validator set while computing total voting power for consumer chain",
			consumerId,
			"error",
			err,
		)
		return
	}
	for _, v := range vals {
		// only consider the voting power of a validator that would receive rewards (i.e., validator has been validating for a number of blocks)
		if !k.IsEligibleForConsumerRewards(ctx, v.JoinHeight) {
			continue
		}

		totalPower += v.Power
	}

	return
}

// IdentifyConsumerIdFromIBCPacket checks if the packet destination matches a registered consumer chain.
// If so, it returns the consumer chain ID, otherwise an error.
func (k Keeper) IdentifyConsumerIdFromIBCPacket(ctx sdk.Context, packet channeltypes.Packet) (string, error) {
	channel, ok := k.channelKeeper.GetChannel(ctx, packet.DestinationPort, packet.DestinationChannel)
	if !ok {
		return "", errorsmod.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for channel ID: %s", packet.DestinationChannel)
	}
	if len(channel.ConnectionHops) != 1 {
		return "", errorsmod.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to consumer chain")
	}
	connectionID := channel.ConnectionHops[0]
	clientId, _, err := k.getUnderlyingClient(ctx, connectionID)
	if err != nil {
		return "", err
	}

	consumerId, found := k.GetClientIdToConsumerId(ctx, clientId)
	if !found {
		return "", errorsmod.Wrapf(types.ErrUnknownConsumerId, "no consumer id for client with id: %s", clientId)
	}

	if _, ok := k.GetConsumerIdToChannelId(ctx, consumerId); !ok {
		return "", errorsmod.Wrapf(types.ErrUnknownConsumerChannelId, "no CCV channel found for chain with ID: %s", consumerId)
	}

	return consumerId, nil
}

// GetSourceChainIdFromIBCPacket returns the chain ID of the chain that sent this packet
func (k Keeper) GetSourceChainIdFromIBCPacket(ctx sdk.Context, packet channeltypes.Packet) (string, error) {
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
	return tmClient.ChainId, nil
}

// HandleSetConsumerCommissionRate sets a per-consumer chain commission rate for the given provider address
// on the condition that the given consumer chain exists.
func (k Keeper) HandleSetConsumerCommissionRate(ctx sdk.Context, consumerId string, providerAddr types.ProviderConsAddress, commissionRate math.LegacyDec) error {
	// check that the consumer chain is active -- registered, initialized, or launched
	if !k.IsConsumerActive(ctx, consumerId) {
		return errorsmod.Wrapf(
			types.ErrInvalidPhase,
			"unknown consumer chain, with id: %s", consumerId)
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
		consumerId,
		providerAddr,
		commissionRate,
	)
}

// TODO: this method needs to be tested
func (k Keeper) ChangeRewardDenoms(ctx sdk.Context, denomsToAdd, denomsToRemove []string) []sdk.Attribute {
	// initialize an empty slice to store event attributes
	eventAttributes := []sdk.Attribute{}

	// loop through denomsToAdd and add each denomination if it is not already registered
	for _, denomToAdd := range denomsToAdd {
		// Log error and move on if one of the denoms is already registered
		if k.ConsumerRewardDenomExists(ctx, denomToAdd) {
			k.Logger(ctx).Error("ChangeRewardDenoms: denom already registered",
				"denomToAdd", denomToAdd,
			)
			continue
		}
		k.SetConsumerRewardDenom(ctx, denomToAdd)

		eventAttributes = append(eventAttributes, sdk.NewAttribute(types.AttributeAddConsumerRewardDenom, denomToAdd))
	}

	// loop through denomsToRemove and remove each denomination if it is registered
	for _, denomToRemove := range denomsToRemove {
		// Log error and move on if one of the denoms is not registered
		if !k.ConsumerRewardDenomExists(ctx, denomToRemove) {
			k.Logger(ctx).Error("ChangeRewardDenoms: denom not registered",
				"denomToRemove", denomToRemove,
			)
			continue
		}
		k.DeleteConsumerRewardDenom(ctx, denomToRemove)

		eventAttributes = append(eventAttributes, sdk.NewAttribute(types.AttributeRemoveConsumerRewardDenom, denomToRemove))
	}

	// return the slice of event attributes
	return eventAttributes
}
