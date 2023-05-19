package keeper

import (
	"fmt"

	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"

	transfertypes "github.com/cosmos/ibc-go/v4/modules/apps/transfer/types"
	channeltypes "github.com/cosmos/ibc-go/v4/modules/core/04-channel/types"

	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// EndBlockRD executes EndBlock logic for the Reward Distribution sub-protocol.
// Reward Distribution follows a simple model: send tokens to the fee pool
// of the provider validator set
func (k Keeper) EndBlockRD(ctx sdk.Context) {
	if !k.shouldNotifyRewardsToProvider(ctx) {
		return
	}

	k.QueueNotifyRewardsPackets(ctx)

	// Update LastTransmissionBlockHeight
	newLtbh := types.LastTransmissionBlockHeight{
		Height: ctx.BlockHeight(),
	}
	k.SetLastTransmissionBlockHeight(ctx, newLtbh)
}

// Check whether it's time to notify rewards to provider
func (k Keeper) shouldNotifyRewardsToProvider(ctx sdk.Context) bool {
	bpdt := k.GetBlocksPerDistributionTransmission(ctx)
	curHeight := ctx.BlockHeight()
	ltbh := k.GetLastTransmissionBlockHeight(ctx)
	return (curHeight - ltbh.Height) >= bpdt
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
