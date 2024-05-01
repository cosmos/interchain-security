package keeper

import (
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// BeginBlockRD executes BeginBlock logic for the Reward Distribution sub-protocol.
func (k Keeper) BeginBlockRD(ctx sdk.Context, req abci.RequestBeginBlock) {
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
func (k Keeper) AllocateTokens(ctx sdk.Context) {
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

		// note that it's possible that no rewards are collected even though the
		// reward pool isn't empty. This can happen if the reward pool holds some tokens
		// of non-whitelisted denominations.
		if rewardsCollected.IsZero() {
			continue
		}

		rewardsCollectedDec := sdk.NewDecCoinsFromCoins(rewardsCollected...)

		// temporary workaround to keep CanWithdrawInvariant happy
		// general discussions here: https://github.com/cosmos/cosmos-sdk/issues/2906#issuecomment-441867634
		feePool := k.distributionKeeper.GetFeePool(ctx)
		if k.ComputeConsumerTotalVotingPower(ctx, consumer.ChainId) == 0 {
			feePool.CommunityPool = feePool.CommunityPool.Add(rewardsCollectedDec...)
			k.distributionKeeper.SetFeePool(ctx, feePool)
			return
		}

		// calculate the reward allocations
		remaining := rewardsCollectedDec
		communityTax := k.distributionKeeper.GetCommunityTax(ctx)
		voteMultiplier := math.LegacyOneDec().Sub(communityTax)
		feeMultiplier := rewardsCollectedDec.MulDecTruncate(voteMultiplier)

		// allocate tokens to consumer validators
		feeAllocated := k.AllocateTokensToConsumerValidators(
			ctx,
			consumer.ChainId,
			feeMultiplier,
		)
		remaining = remaining.Sub(feeAllocated)

		// allocate community funding
		feePool.CommunityPool = feePool.CommunityPool.Add(remaining...)
		k.distributionKeeper.SetFeePool(ctx, feePool)
	}
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
	totalPower := k.ComputeConsumerTotalVotingPower(ctx, chainID)
	if totalPower == 0 {
		return allocated
	}

	// Allocate tokens by iterating over the consumer validators
	for _, consumerVal := range k.GetConsumerValSet(ctx, chainID) {
		consAddr := sdk.ConsAddress(consumerVal.ProviderConsAddr)

		// get the validator tokens fraction using its voting power
		powerFraction := math.LegacyNewDec(consumerVal.Power).QuoTruncate(math.LegacyNewDec(totalPower))
		tokensFraction := tokens.MulDecTruncate(powerFraction)

		// get the validator type struct for the consensus address
		val := k.stakingKeeper.ValidatorByConsAddr(ctx, consAddr).(stakingtypes.Validator)

		// check if the validator set a custom commission rate for the consumer chain
		if cr, found := k.GetConsumerCommissionRate(ctx, chainID, types.NewProviderConsAddress(consAddr)); found {
			// set the validator commission rate
			val.Commission.CommissionRates.Rate = cr
		}

		// allocate the consumer reward tokens to the validator
		k.distributionKeeper.AllocateTokensToValidator(
			ctx,
			val,
			tokensFraction,
		)

		// sum the tokens allocated
		allocated = allocated.Add(tokensFraction...)
	}

	return allocated
}

// TransferConsumerRewardsToDistributionModule transfers the rewards allocation of the given consumer chain
// from the consumer rewards pool to a the distribution module
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
	// sum the opted-in validators set voting powers
	for _, v := range k.GetConsumerValSet(ctx, chainID) {
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
func (k Keeper) HandleSetConsumerCommissionRate(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress, commissionRate sdk.Dec) error {
	// check that the consumer chain exists
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"unknown consumer chain, with id: %s", chainID)
	}

	// validate against the minimum commission rate
	minRate := k.stakingKeeper.MinCommissionRate(ctx)
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
