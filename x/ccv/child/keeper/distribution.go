package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	transfertypes "github.com/cosmos/ibc-go/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/modules/core/04-channel/types"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// Simple model, donate tokens to the fee pool of the provider validator set
// reference: cosmos/ibc-go/modules/apps/transfer/keeper/msg_server.go
func (k Keeper) DistributeToProviderValidatorSet(ctx sdk.Context) error {
	if !k.shouldTransmit(ctx) {
		return nil
	}

	// work around to reuse the IBC token transfer logic
	consumerFeePoolAddr := k.accountKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
	tokens := k.bankKeeper.GetAllBalances(ctx, consumerFeePoolAddr)
	for _, token := range tokens {
		err := k.ibcTransferKeeper.SendTransfer(ctx,
			transfertypes.PortID,
			k.GetDistributionTransmissionChannel(ctx),
			token,
			consumerFeePoolAddr,
			k.GetProviderFeePoolAddrStr(ctx),
			clienttypes.Height{0, 0},
			uint64(ccv.GetTimeoutTimestamp(ctx.BlockTime()).UnixNano()),
		)
		if err != nil {
			return err
		}
	}
	return nil
}

// test to see if enough blocks have passed for
// a transmission to occur
func (k Keeper) shouldTransmit(ctx sdk.Context) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.LastDistributionTransmissionKey)
	if bz == nil {
		return true
	}
	ltbh := &types.LastTransmissionBlockHeight{}
	ltbh.Unmarshal(bz)
	bpdt := k.GetBlocksPerDistributionTransmission(ctx)
	curHeight := ctx.BlockHeight()
	return (curHeight - ltbh.Height) >= bpdt
}

func (k Keeper) ChannelOpenInit(ctx sdk.Context, msg *channeltypes.MsgChannelOpenInit) (
	*channeltypes.MsgChannelOpenInitResponse, error) {
	return k.ibcCoreKeeper.ChannelOpenInit(sdk.WrapSDKContext(ctx), msg)
}
