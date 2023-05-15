package keeper

import (
	"fmt"
	"strconv"

	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"

	transfertypes "github.com/cosmos/ibc-go/v4/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v4/modules/core/04-channel/types"

	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// EndBlockRD executes EndBlock logic for the Reward Distribution sub-protocol.
// Reward Distribution follows a simple model: send tokens to the fee pool
// of the provider validator set
func (k Keeper) EndBlockRD(ctx sdk.Context) {
	// Split blocks rewards.
	// It panics in case of marshalling / unmarshalling errors or
	// if sending coins between module accounts fails.
	k.DistributeRewardsInternally(ctx)

	if !k.shouldSendRewardsToProvider(ctx) {
		return
	}

	// Try to send rewards to provider
	cachedCtx, writeCache := ctx.CacheContext()
	if err := k.SendRewardsToProvider(cachedCtx); err != nil {
		k.Logger(ctx).Error("attempt to sent rewards to provider failed", "error", err)
	} else {
		// The cached context is created with a new EventManager so we merge the event
		// into the original context
		ctx.EventManager().EmitEvents(cachedCtx.EventManager().Events())
		// write cache
		writeCache()
	}

	// Update LastTransmissionBlockHeight
	newLtbh := types.LastTransmissionBlockHeight{
		Height: ctx.BlockHeight(),
	}
	k.SetLastTransmissionBlockHeight(ctx, newLtbh)
}

// DistributeRewardsInternally splits the block rewards according to the
// ConsumerRedistributionFrac param.
// Returns true if it's time to send rewards to provider
func (k Keeper) DistributeRewardsInternally(ctx sdk.Context) {
	consumerFeePoolAddr := k.authKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
	fpTokens := k.bankKeeper.GetAllBalances(ctx, consumerFeePoolAddr)

	// split the fee pool, send the consumer's fraction to the consumer redistribution address
	frac, err := sdk.NewDecFromStr(k.GetConsumerRedistributionFrac(ctx))
	if err != nil {
		// ConsumerRedistributionFrac was already validated when set as a param
		panic(fmt.Errorf("ConsumerRedistributionFrac is invalid: %w", err))
	}
	decFPTokens := sdk.NewDecCoinsFromCoins(fpTokens...)
	// NOTE the truncated decimal remainder will be sent to the provider fee pool
	consRedistrTokens, _ := decFPTokens.MulDec(frac).TruncateDecimal()
	err = k.bankKeeper.SendCoinsFromModuleToModule(ctx, k.feeCollectorName,
		types.ConsumerRedistributeName, consRedistrTokens)
	if err != nil {
		// SendCoinsFromModuleToModule will panic if either module account does not exist,
		// while SendCoins (called inside) returns an error upon failure.
		// It is the common behavior in cosmos-sdk to panic if SendCoinsFromModuleToModule
		// returns error.
		panic(err)
	}

	// Send the remainder to the Provider fee pool over ibc. Buffer these
	// through a secondary address on the consumer chain to ensure that the
	// tokens do not go through the consumer redistribute split twice in the
	// event that the transfer fails the tokens are returned to the consumer
	// chain.
	remainingTokens := fpTokens.Sub(consRedistrTokens)
	err = k.bankKeeper.SendCoinsFromModuleToModule(ctx, k.feeCollectorName,
		types.ConsumerToSendToProviderName, remainingTokens)
	if err != nil {
		// SendCoinsFromModuleToModule will panic if either module account does not exist,
		// while SendCoins (called inside) returns an error upon failure.
		// It is the common behavior in cosmos-sdk to panic if SendCoinsFromModuleToModule
		// returns error.
		panic(err)
	}
}

// Check whether it's time to send rewards to provider
func (k Keeper) shouldSendRewardsToProvider(ctx sdk.Context) bool {
	bpdt := k.GetBlocksPerDistributionTransmission(ctx)
	curHeight := ctx.BlockHeight()
	ltbh := k.GetLastTransmissionBlockHeight(ctx)
	return (curHeight - ltbh.Height) >= bpdt
}

// SendRewardsToProvider attempts to send to the provider (via IBC)
// all the block rewards allocated for the provider
func (k Keeper) SendRewardsToProvider(ctx sdk.Context) error {
	// empty out the toSendToProviderTokens address
	ch := k.GetDistributionTransmissionChannel(ctx)
	transferChannel, found := k.channelKeeper.GetChannel(ctx, transfertypes.PortID, ch)
	if found && transferChannel.State == channeltypes.OPEN {
		tstProviderAddr := k.authKeeper.GetModuleAccount(ctx,
			types.ConsumerToSendToProviderName).GetAddress()
		providerAddr := k.GetProviderFeePoolAddrStr(ctx)
		timeoutHeight := clienttypes.ZeroHeight()
		transferTimeoutPeriod := k.GetTransferTimeoutPeriod(ctx)
		timeoutTimestamp := uint64(ctx.BlockTime().Add(transferTimeoutPeriod).UnixNano())

		sentCoins := sdk.NewCoins()

		// iterate over all whitelisted reward denoms
		for _, denom := range k.AllowedRewardDenoms(ctx) {
			// get the balance of the denom in the toSendToProviderTokens address
			balance := k.bankKeeper.GetBalance(ctx, tstProviderAddr, denom)

			// if the balance is not zero,
			if !balance.IsZero() {
				// send the balance to the provider
				err := k.ibcTransferKeeper.SendTransfer(ctx,
					transfertypes.PortID,
					ch,
					balance,
					tstProviderAddr,
					providerAddr,
					timeoutHeight,
					timeoutTimestamp,
				)
				if err != nil {
					return err
				}
				sentCoins = sentCoins.Add(balance)
			}
		}

		consumerFeePoolAddr := k.authKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
		fpTokens := k.bankKeeper.GetAllBalances(ctx, consumerFeePoolAddr)

		k.Logger(ctx).Info("sent block rewards to provider",
			"total fee pool", fpTokens.String(),
			"sent", sentCoins.String(),
		)
		currentHeight := ctx.BlockHeight()
		ctx.EventManager().EmitEvent(
			sdk.NewEvent(
				ccv.EventTypeFeeDistribution,
				sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
				sdk.NewAttribute(ccv.AttributeDistributionCurrentHeight, strconv.Itoa(int(currentHeight))),
				sdk.NewAttribute(ccv.AttributeDistributionNextHeight, strconv.Itoa(int(currentHeight+k.GetBlocksPerDistributionTransmission(ctx)))),
				sdk.NewAttribute(ccv.AttributeDistributionFraction, (k.GetConsumerRedistributionFrac(ctx))),
				sdk.NewAttribute(ccv.AttributeDistributionTotal, fpTokens.String()),
				sdk.NewAttribute(ccv.AttributeDistributionToProvider, sentCoins.String()),
			),
		)
	}

	return nil
}

// AllowedRewardDenoms returns a list of all denoms that are allowed
// to be sent to the provider as rewards
func (k Keeper) AllowedRewardDenoms(ctx sdk.Context) []string {
	var rewardDenoms []string

	// first, append the native reward denoms
	rewardDenoms = append(rewardDenoms, k.GetRewardDenoms(ctx)...)

	// then, append the provider-originated reward denoms
	for _, denom := range k.GetProviderRewardDenoms(ctx) {
		// every provider denom was sent over IBC,
		// so we must prefix the denom
		sourcePrefix := transfertypes.GetDenomPrefix(
			transfertypes.PortID,
			k.GetDistributionTransmissionChannel(ctx),
		)
		// NOTE: sourcePrefix contains the trailing "/"
		prefixedDenom := sourcePrefix + denom
		// construct the denomination trace from the full raw denomination
		denomTrace := transfertypes.ParseDenomTrace(prefixedDenom)

		// append the IBC denom to the list of allowed reward denoms
		rewardDenoms = append(rewardDenoms, denomTrace.IBCDenom())
	}

	return rewardDenoms
}

func (k Keeper) GetLastTransmissionBlockHeight(ctx sdk.Context) types.LastTransmissionBlockHeight {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.LastDistributionTransmissionKey())
	ltbh := types.LastTransmissionBlockHeight{}
	if bz != nil {
		if err := ltbh.Unmarshal(bz); err != nil {
			panic(fmt.Errorf("failed to unmarshal LastTransmissionBlockHeight: %w", err))
		}
	}
	return ltbh
}

func (k Keeper) SetLastTransmissionBlockHeight(ctx sdk.Context, ltbh types.LastTransmissionBlockHeight) {
	store := ctx.KVStore(k.storeKey)
	bz, err := ltbh.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal LastTransmissionBlockHeight: %w", err))
	}
	store.Set(types.LastDistributionTransmissionKey(), bz)
}

func (k Keeper) ChannelOpenInit(ctx sdk.Context, msg *channeltypes.MsgChannelOpenInit) (
	*channeltypes.MsgChannelOpenInitResponse, error,
) {
	return k.ibcCoreKeeper.ChannelOpenInit(sdk.WrapSDKContext(ctx), msg)
}

func (k Keeper) TransferChannelExists(ctx sdk.Context, channelID string) bool {
	_, found := k.channelKeeper.GetChannel(ctx, transfertypes.PortID, channelID)
	return found
}

func (k Keeper) GetConnectionHops(ctx sdk.Context, srcPort, srcChan string) ([]string, error) {
	ch, found := k.channelKeeper.GetChannel(ctx, srcPort, srcChan)
	if !found {
		return []string{}, errorsmod.Wrapf(ccv.ErrChannelNotFound,
			"cannot get connection hops from non-existent channel")
	}
	return ch.ConnectionHops, nil
}

// GetEstimatedNextFeeDistribution returns data about next fee distribution. Data represents an estimation of
// accumulated fees at the current block height.
func (k Keeper) GetEstimatedNextFeeDistribution(ctx sdk.Context) types.NextFeeDistributionEstimate {
	lastH := k.GetLastTransmissionBlockHeight(ctx)
	nextH := lastH.GetHeight() + k.GetBlocksPerDistributionTransmission(ctx)

	consumerFeePoolAddr := k.authKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
	total := k.bankKeeper.GetAllBalances(ctx, consumerFeePoolAddr)

	fracParam := k.GetConsumerRedistributionFrac(ctx)
	frac, err := sdk.NewDecFromStr(fracParam)
	if err != nil {
		// ConsumerRedistributionFrac was already validated when set as a param
		panic(fmt.Errorf("ConsumerRedistributionFrac is invalid: %w", err))
	}

	totalTokens := sdk.NewDecCoinsFromCoins(total...)
	// truncated decimals are implicitly added to provider
	consumerTokens, _ := totalTokens.MulDec(frac).TruncateDecimal()
	providerTokens := total.Sub(consumerTokens)

	return types.NextFeeDistributionEstimate{
		CurrentHeight:        ctx.BlockHeight(),
		LastHeight:           lastH.GetHeight(),
		NextHeight:           nextH,
		DistributionFraction: fracParam,
		Total:                totalTokens.String(),
		ToProvider:           sdk.NewDecCoinsFromCoins(providerTokens...).String(),
		ToConsumer:           sdk.NewDecCoinsFromCoins(consumerTokens...).String(),
	}
}
