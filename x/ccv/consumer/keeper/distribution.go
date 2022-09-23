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

// TODO
// return 3 numbers
// last one -> we have that
// next one -> add the interval to it
// next interval -> the interval to add
// Simple model, send tokens to the fee pool of the provider validator set
// reference: cosmos/ibc-go/v3/modules/apps/transfer/keeper/msg_server.go
func (k Keeper) DistributeToProviderValidatorSet(ctx sdk.Context) error {

	ltbh, err := k.GetLastTransmissionBlockHeight(ctx) // TODO: rename Transmission -> Distribution(BlockHeight)
	if err != nil {
		return err
	}

	consumerFeePoolAddr := k.authKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
	fpTokens := k.bankKeeper.GetAllBalances(ctx, consumerFeePoolAddr)

	// split the fee pool, send the consumer's fraction to the consumer redistribution address
	frac, err := sdk.NewDecFromStr(ConsumerRedistributeFrac)
	if err != nil {
		return err
	}
	decFPTokens := sdk.NewDecCoinsFromCoins(fpTokens...)
	// NOTE the truncated decimal remainder will be sent to the provider fee pool
	consRedistrTokens, _ := decFPTokens.MulDec(frac).TruncateDecimal()
	err = k.bankKeeper.SendCoinsFromModuleToModule(ctx, k.feeCollectorName,
		types.ConsumerRedistributeName, consRedistrTokens)
	if err != nil {
		return err
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
		return err
	}
	// TODO:
	// check account balance for for prov:types.ConsumerToSendToProviderName; for cons: types.ConsumerRedistributeName
	// also return sum

	bpdt := k.GetBlocksPerDistributionTransmission(ctx)
	curHeight := ctx.BlockHeight()

	if (curHeight - ltbh.Height) < bpdt {
		// not enough blocks have passed for  a transmission to occur
		return nil
	}

	// empty out the toSendToProviderTokens address
	ch := k.GetDistributionTransmissionChannel(ctx)
	transferChannel, found := k.channelKeeper.GetChannel(ctx, transfertypes.PortID, ch)
	if found && transferChannel.State == channeltypes.OPEN {
		tstProviderAddr := k.authKeeper.GetModuleAccount(ctx,
			types.ConsumerToSendToProviderName).GetAddress()
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

func (k Keeper) GetLastDistributionBlockHeight(ctx sdk.Context) (
	*types.LastTransmissionBlockHeight, error) {

	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.LastDistributionBlockHeightKey())
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
	store.Set(types.LastDistributionBlockHeightKey(), bz)
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
