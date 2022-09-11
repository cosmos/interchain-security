package keeper

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

const TransferTimeDelay = 1 * 7 * 24 * time.Hour // 1 weeks

// The fraction of tokens allocated to the consumer redistribution address
// during distribution events. The fraction is a string representing a
// decimal number. For example "0.75" would represent 75%.
const ConsumerRedistributeFrac = "0.75"

// Simple model, send tokens to the fee pool of the provider validator set
// reference: cosmos/ibc-go/v3/modules/apps/transfer/keeper/msg_server.go
func (k Keeper) DistributeToProviderValidatorSet(ctx sdk.Context) error {
	// Get the address of the consumer fee pool, and get the tokens it currently contains
	consumerFeePoolAddr := k.authKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
	fpTokens := k.bankKeeper.GetAllBalances(ctx, consumerFeePoolAddr)

	// Get the fraction of rewards and fees that will be kept by the consumer
	frac, err := sdk.NewDecFromStr(ConsumerRedistributeFrac)
	if err != nil {
		return err
	}

	// Split the fee tokens and send the ones that will remain on the consumer
	// to the consumer redistribute account. TruncateDecimal leaves a remainder.
	// We ignore it here and this remainder will be sent to the provider below.
	decFPTokens := sdk.NewDecCoinsFromCoins(fpTokens...)
	consRedistrTokens, _ := decFPTokens.MulDec(frac).TruncateDecimal()
	err = k.bankKeeper.SendCoinsFromModuleToModule(ctx, k.feeCollectorName,
		types.ConsumerRedistributeName, consRedistrTokens)
	if err != nil {
		return err
	}

	// Send the rest of the tokens to the SendToProvider buffer address.
	remainingTokens := fpTokens.Sub(consRedistrTokens)
	err = k.bankKeeper.SendCoinsFromModuleToModule(ctx, k.feeCollectorName,
		types.SendToProviderName, remainingTokens)
	if err != nil {
		return err
	}

	// Check if enough blocks have passed to send a reward transfer.
	ltbh, err := k.GetLastTransmissionBlockHeight(ctx)
	if err != nil {
		return err
	}
	bpdt := k.GetBlocksPerDistributionTransmission(ctx)
	curHeight := ctx.BlockHeight()
	if (curHeight - ltbh.Height) < bpdt {
		// not enough blocks have passed for  a transmission to occur
		return nil
	}

	// Send tokens in SendToProvider account to the provider.
	// If this fails for some reason, the tokens will stay in the SendToProvider account,
	// and will end up getting sent whenever it next works.
	ch := k.GetDistributionTransmissionChannel(ctx)
	transferChannel, found := k.channelKeeper.GetChannel(ctx, transfertypes.PortID, ch)
	if found && transferChannel.State == channeltypes.OPEN {
		tstProviderAddr := k.authKeeper.GetModuleAccount(ctx,
			types.SendToProviderName).GetAddress()
		tstProviderTokens := k.bankKeeper.GetAllBalances(ctx, tstProviderAddr)
		providerAddr := k.GetProviderFeePoolAddrStr(ctx)
		timeoutHeight := clienttypes.ZeroHeight()
		timeoutTimestamp := uint64(ctx.BlockTime().Add(TransferTimeDelay).UnixNano())
		for _, token := range tstProviderTokens {
			err := k.ibcTransferKeeper.SendTransfer(ctx,
				transfertypes.PortID,
				ch,
				token,
				tstProviderAddr,
				providerAddr,
				timeoutHeight,
				timeoutTimestamp,
			)
			if err != nil {
				return err
			}
		}
	}

	newLtbh := types.LastTransmissionBlockHeight{
		Height: ctx.BlockHeight(),
	}

	return k.SetLastTransmissionBlockHeight(ctx, newLtbh)
}

func (k Keeper) GetLastTransmissionBlockHeight(ctx sdk.Context) (
	*types.LastTransmissionBlockHeight, error) {

	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.LastDistributionTransmissionKey())
	ltbh := &types.LastTransmissionBlockHeight{}
	if bz != nil {
		err := ltbh.Unmarshal(bz)
		if err != nil {
			return ltbh, err
		}
	}
	return ltbh, nil
}

func (k Keeper) SetLastTransmissionBlockHeight(ctx sdk.Context,
	ltbh types.LastTransmissionBlockHeight) error {

	store := ctx.KVStore(k.storeKey)
	bz, err := ltbh.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.LastDistributionTransmissionKey(), bz)
	return nil
}

func (k Keeper) ChannelOpenInit(ctx sdk.Context, msg *channeltypes.MsgChannelOpenInit) (
	*channeltypes.MsgChannelOpenInitResponse, error) {
	return k.ibcCoreKeeper.ChannelOpenInit(sdk.WrapSDKContext(ctx), msg)
}

func (k Keeper) GetConnectionHops(ctx sdk.Context, srcPort, srcChan string) ([]string, error) {
	ch, found := k.channelKeeper.GetChannel(ctx, srcPort, srcChan)
	if !found {
		return []string{}, sdkerrors.Wrapf(ccv.ErrChannelNotFound,
			"cannot get connection hops from non-existent channel")
	}
	return ch.ConnectionHops, nil
}
