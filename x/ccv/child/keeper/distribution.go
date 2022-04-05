package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	"github.com/cosmos/interchain-security/x/ccv/child/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// Simple model, send tokens to the fee pool of the provider validator set
// reference: cosmos/ibc-go/v3/modules/apps/transfer/keeper/msg_server.go
func (k Keeper) DistributeToProviderValidatorSet(ctx sdk.Context) error {

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

	// work around to reuse the IBC token transfer logic
	consumerFeePoolAddr := k.accountKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
	fpTokens := k.bankKeeper.GetAllBalances(ctx, consumerFeePoolAddr)

	// split the fee pool, send the consumer's fraction to the consumer redistribution address
	fracStr := k.GetConsumerRedistributeFrac(ctx)
	frac, err := sdk.NewDecFromStr(fracStr)
	if err != nil {
		return err
	}
	decFPTokens := sdk.NewDecCoinsFromCoins(fpTokens...)
	consRedistrTokens, _ := decFPTokens.MulDec(frac).TruncateDecimal()
	err = k.bankKeeper.SendCoinsFromModuleToModule(ctx, k.feeCollectorName, types.ConsumerRedistributeName, consRedistrTokens)
	if err != nil {
		return err
	}

	// Send the remainder to the Provider fee pool over ibc
	remainingTokens := fpTokens.Sub(consRedistrTokens)
	ch := k.GetDistributionTransmissionChannel(ctx)
	providerAddr := k.GetProviderFeePoolAddrStr(ctx)
	timeoutHeight := clienttypes.Height{0, 0}
	timeoutTimestamp := uint64(ccv.GetTimeoutTimestamp(ctx.BlockTime()).UnixNano())
	for _, token := range remainingTokens {
		err := k.ibcTransferKeeper.SendTransfer(ctx,
			transfertypes.PortID,
			ch,
			token,
			consumerFeePoolAddr,
			providerAddr,
			timeoutHeight,
			timeoutTimestamp,
		)
		if err != nil {
			return err
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
	bz := store.Get(types.LastDistributionTransmissionKey)
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
	store.Set(types.LastDistributionTransmissionKey, bz)
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
