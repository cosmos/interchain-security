package keeper

import (
	"fmt"

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
	//fmt.Println("DistributeToProviderValidatorSet called")

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

	fmt.Println("debug about to distribute")
	fmt.Printf(
		"distribution log:\nltbh:%v\nbpdt:%v\ncurrHeight:%v\n(curHeight - ltbh.Height) < bpdt:%v\n",
		ltbh.Height, bpdt, curHeight, (curHeight-ltbh.Height) < bpdt)

	// work around to reuse the IBC token transfer logic
	consumerFeePoolAddr := k.accountKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
	tokens := k.bankKeeper.GetAllBalances(ctx, consumerFeePoolAddr)
	for _, token := range tokens {
		fmt.Printf("debug GetDistributionTransmissionChannel: %v\n", k.GetDistributionTransmissionChannel(ctx))
		fmt.Printf("debug transfertypes.PortID: %v\n", transfertypes.PortID)
		fmt.Printf("debug token: %v\n", token)
		fmt.Printf("debug consumerFeePoolAddr: %s\n", consumerFeePoolAddr)
		fmt.Printf("debug k.GetProviderFeePoolAddrStr(ctx): %v\n", k.GetProviderFeePoolAddrStr(ctx))
		fmt.Printf("debug events len distribute %v\n", len(ctx.EventManager().Events()))
		err := k.ibcTransferKeeper.SendTransfer(ctx,
			transfertypes.PortID,
			k.GetDistributionTransmissionChannel(ctx),
			token,
			consumerFeePoolAddr,
			k.GetProviderFeePoolAddrStr(ctx),
			clienttypes.Height{0, 0},
			uint64(ccv.GetTimeoutTimestamp(ctx.BlockTime()).UnixNano()),
		)

		balance := k.bankKeeper.GetBalance(ctx, consumerFeePoolAddr, "stake")
		fmt.Printf("debug ibc-go sender stake (distr): %s\n", balance)

		if err != nil {
			panic(err)
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
