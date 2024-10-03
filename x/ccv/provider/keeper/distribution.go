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

// GetAllowlistedRewardDenoms returns the allowlisted reward denom for the given consumer id.
func (k Keeper) GetAllowlistedRewardDenoms(ctx sdk.Context, consumerId string) ([]string, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToAllowlistedRewardDenomKey(consumerId))
	if bz == nil {
		return []string{}, nil
	}

	var denoms types.AllowlistedRewardDenoms
	if err := denoms.Unmarshal(bz); err != nil {
		return []string{}, err
	}
	return denoms.Denoms, nil
}

// SetAllowlistedRewardDenoms sets the allowlisted reward denoms for the given consumer id.
func (k Keeper) SetAllowlistedRewardDenoms(ctx sdk.Context, consumerId string, rewardDenoms []string) error {
	store := ctx.KVStore(k.storeKey)
	allowlistedUpdatedDenoms := types.AllowlistedRewardDenoms{Denoms: rewardDenoms}
	bz, err := allowlistedUpdatedDenoms.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.ConsumerIdToAllowlistedRewardDenomKey(consumerId), bz)
	return nil
}

// DeleteAllowlistedRewardDenoms deletes the allowlisted reward denom for the given consumer id.
func (k Keeper) DeleteAllowlistedRewardDenoms(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToAllowlistedRewardDenomKey(consumerId))
}

// UpdateAllowlistedRewardDenoms updates the allowlisted reward denoms for this consumer chain with the provided `rewardDenoms`
func (k Keeper) UpdateAllowlistedRewardDenoms(ctx sdk.Context, consumerId string, rewardDenoms []string) error {
	k.DeleteAllowlistedRewardDenoms(ctx, consumerId)
	return k.SetAllowlistedRewardDenoms(ctx, consumerId, rewardDenoms)
}

// GetConsumerRewardsAllocationByDenom returns the consumer rewards allocation for the given consumer id and denom
func (k Keeper) GetConsumerRewardsAllocationByDenom(ctx sdk.Context, consumerId string, denom string) (types.ConsumerRewardsAllocation, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerRewardsAllocationByDenomKey(consumerId, denom))

	var rewardsAllocation types.ConsumerRewardsAllocation
	err := rewardsAllocation.Unmarshal(bz)
	if err != nil {
		return types.ConsumerRewardsAllocation{}, err
	}

	return rewardsAllocation, nil
}

// SetConsumerRewardsAllocationByDenom sets the consumer rewards allocation for the given consumer id and denom
func (k Keeper) SetConsumerRewardsAllocationByDenom(ctx sdk.Context, consumerId string, denom string, rewardsAllocation types.ConsumerRewardsAllocation) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := rewardsAllocation.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.ConsumerRewardsAllocationByDenomKey(consumerId, denom), bz)
	return nil
}

// DeleteConsumerRewardsAllocationByDenom deletes the consumer rewards allocation for the given consumer id and denom
func (k Keeper) DeleteConsumerRewardsAllocationByDenom(ctx sdk.Context, consumerId string, denom string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerRewardsAllocationByDenomKey(consumerId, denom))
}

// AllocateConsumerRewards allocates the given rewards to provider consumer chain with the given consumer id
func (k Keeper) AllocateConsumerRewards(ctx sdk.Context, consumerId string, alloc types.ConsumerRewardsAllocation) (types.ConsumerRewardsAllocation, error) {

	chainId, err := k.GetConsumerChainId(ctx, consumerId)
	if err != nil {
		k.Logger(ctx).Error(
			"cannot get consumer chain id in AllocateConsumerRewards",
			"consumerId", consumerId,
			"error", err.Error(),
		)
		return types.ConsumerRewardsAllocation{}, err
	}

	// temporary workaround to keep CanWithdrawInvariant happy
	// general discussions here: https://github.com/cosmos/cosmos-sdk/issues/2906#issuecomment-441867634
	if k.ComputeConsumerTotalVotingPower(ctx, consumerId) == 0 {
		rewardsToSend, rewardsChange := alloc.Rewards.TruncateDecimal()
		err := k.distributionKeeper.FundCommunityPool(context.Context(ctx), rewardsToSend, k.accountKeeper.GetModuleAccount(ctx, types.ConsumerRewardsPool).GetAddress())
		if err != nil {
			k.Logger(ctx).Error(
				"fail to allocate ICS rewards to community pool",
				"consumerId", consumerId,
				"chainId", chainId,
				"error", err.Error(),
			)
		}
		k.Logger(ctx).Info(
			"allocated ICS rewards to community pool",
			"consumerId", consumerId,
			"chainId", chainId,
			"amount", rewardsToSend.String(),
		)

		// set the consumer allocation to the remaining reward decimals
		alloc.Rewards = rewardsChange

		return alloc, nil
	}

	// Consumer rewards are distributed between the validators and the community pool.
	// The decimals resulting from the distribution are expected to remain in the consumer reward allocations.

	communityTax, err := k.distributionKeeper.GetCommunityTax(ctx)
	if err != nil {
		k.Logger(ctx).Error(
			"cannot get community tax while allocating ICS rewards",
			"consumerId", consumerId,
			"chainId", chainId,
			"error", err.Error(),
		)
		return types.ConsumerRewardsAllocation{}, err
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
			"cannot send ICS rewards to distribution module account",
			"consumerId", consumerId,
			"chainId", chainId,
			"error", err.Error(),
		)
		return types.ConsumerRewardsAllocation{}, err
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
			"fail to allocate ICS rewards to community pool",
			"consumerId", consumerId,
			"chainId", chainId,
			"error", err.Error(),
		)
		return types.ConsumerRewardsAllocation{}, err
	}

	// set consumer allocations to the remaining rewards decimals
	alloc.Rewards = validatorsRewardsChange.Add(remainingChanges...)

	k.Logger(ctx).Info(
		"distributed ICS rewards successfully",
		"consumerId", consumerId,
		"chainId", chainId,
		"total-rewards", consumerRewards.String(),
		"sent-to-validators", validatorsRewardsTrunc.String(),
		"sent-to-CP", remainingRewards.String(),
	)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			types.EventTypeDistributedRewards,
			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
			sdk.NewAttribute(types.AttributeConsumerId, consumerId),
			sdk.NewAttribute(types.AttributeConsumerChainId, chainId),
			sdk.NewAttribute(types.AttributeRewardTotal, consumerRewards.String()),
			sdk.NewAttribute(types.AttributeRewardDistributed, validatorsRewardsTrunc.String()),
			sdk.NewAttribute(types.AttributeRewardCommunityPool, remainingRewards.String()),
		),
	)
	return alloc, nil
}

// AllocateTokens performs rewards distribution to the community pool and validators
// based on the Partial Set Security distribution specification.
func (k Keeper) AllocateTokens(ctx sdk.Context) {
	// return if there is no coins in the consumer rewards pool
	if k.GetConsumerRewardsPool(ctx).IsZero() {
		return
	}

	// Iterate over all launched consumer chains.
	// To avoid large iterations over all the consumer IDs, iterate only over
	// chains with an IBC client created.
	allConsumerRewardDenoms := k.GetAllConsumerRewardDenoms(ctx) // corresponds to allowlisted denoms that were allowlisted through governance
	for _, consumerId := range k.GetAllConsumersWithIBCClients(ctx) {
		// also consider this chain's allowlisted reward denoms
		consumerAllowlistedRewardDenoms, err := k.GetAllowlistedRewardDenoms(ctx, consumerId)
		if err != nil {
			k.Logger(ctx).Error(
				"fail to retrieve the allowlisted reward denoms for consumer chain",
				"consumer id", consumerId,
				"error", err.Error())
			continue
		}

		allAllowlistedDenoms := append(allConsumerRewardDenoms, consumerAllowlistedRewardDenoms...)
		for _, denom := range allAllowlistedDenoms {
			// use a cached context to verify that the call to `AllocateConsumerRewards` is atomic, and hence
			// all transfers in `AllocateConsumerRewards` happen all together or not at all.
			cachedCtx, writeCache := ctx.CacheContext()
			consumerRewards, err := k.GetConsumerRewardsAllocationByDenom(cachedCtx, consumerId, denom)
			if err != nil {
				k.Logger(ctx).Error(
					"failed to get the consumer rewards allocation for this denom",
					"consumer id", consumerId,
					"denom", denom,
					"error", err.Error(),
				)
				continue
			}
			remainingRewardDec, err := k.AllocateConsumerRewards(cachedCtx, consumerId, consumerRewards)
			if err != nil {
				k.Logger(ctx).Error(
					"fail to allocate rewards for consumer chain",
					"consumer id", consumerId,
					"error", err.Error(),
				)
				continue
			}
			err = k.SetConsumerRewardsAllocationByDenom(cachedCtx, consumerId, denom, remainingRewardDec)
			if err != nil {
				k.Logger(ctx).Error(
					"fail to set rewards for consumer chain",
					"consumer id", consumerId,
					"error", err.Error(),
				)
				continue
			}
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
