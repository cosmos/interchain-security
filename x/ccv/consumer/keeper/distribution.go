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
// TODO: Shouldn't this be passed in when instantiating the keeper in app.go?
const ConsumerRedistributeFrac = "0.75"

// Simple model, send tokens to the fee pool of the provider validator set
// reference: cosmos/ibc-go/v3/modules/apps/transfer/keeper/msg_server.go
func (k Keeper) DistributeToProviderValidatorSet(ctx sdk.Context) error {

	// Find out when we last ran this function
	ltbh, err := k.GetLastTransmissionBlockHeight(ctx)
	if err != nil {
		return err
	}

	// We only distribute once every BlocksPerDistributionTransmission blocks
	bpdt := k.GetBlocksPerDistributionTransmission(ctx)
	curHeight := ctx.BlockHeight()

	if (curHeight - ltbh.Height) < bpdt {
		// not enough blocks have passed for  a transmission to occur
		return nil
	}

	// consumerFeePoolAddr
	feeCollectorAccount := k.authKeeper.GetModuleAccount(ctx, k.feeCollectorName).GetAddress()
	feeTokens := k.bankKeeper.GetAllBalances(ctx, feeCollectorAccount)

	// Split the fee pool, send the consumer's fraction to the consumer redistribution address
	frac, err := sdk.NewDecFromStr(ConsumerRedistributeFrac)
	if err != nil {
		return err
	}
	decFeeTokens := sdk.NewDecCoinsFromCoins(feeTokens...)

	// NOTE the truncated decimal remainder will be sent to the provider fee pool
	consRedistrTokens, _ := decFeeTokens.MulDec(frac).TruncateDecimal()
	// Send the coins that will stay with the consumer to the consumer redistribute module account
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
	// TODO: couldn't we find the remainingTokens by simply querying k.bankKeeper.GetAllBalances(ctx, feeCollectorAccount) again?
	remainingTokens := feeTokens.Sub(consRedistrTokens)
	err = k.bankKeeper.SendCoinsFromModuleToModule(ctx, k.feeCollectorName,
		types.ConsumerToSendToProviderName, remainingTokens)
	if err != nil {
		return err
	}

	// Find the number of tokens in the ToSendToProvider account
	tstProviderAddr := k.authKeeper.GetModuleAccount(ctx,
		types.ConsumerToSendToProviderName).GetAddress()
	tstProviderTokens := k.bankKeeper.GetAllBalances(ctx, tstProviderAddr)

	// Send all tokens in the ToSendToProvider account to the provider over IBC
	// As mentioned above, if the send fails for some reason, the tokens will be sent
	// the next time this function runs.
	ch := k.GetDistributionTransmissionChannel(ctx)
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

	// Save the LastTransmissionBlockHeight for next time
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
