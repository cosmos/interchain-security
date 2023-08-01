package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctm "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

func (k Keeper) GetProviderChainInfo(ctx sdk.Context) (*types.QueryProviderInfoResponse, error) {
	//  get the channelID for the channel to the provider.
	consumerChannelID, found := k.GetProviderChannel(ctx)
	if !found {
		return nil, nil
	}
	consumerChannel, found := k.channelKeeper.GetChannel(ctx, ccvtypes.ConsumerPortID, consumerChannelID)
	if !found {
		return nil, nil
	}

	// from channel get connection
	_, consumerConnection, err := k.channelKeeper.GetChannelConnection(ctx, ccvtypes.ConsumerPortID, consumerChannelID)
	if err != nil {
		return nil, err
	}

	providerChannelID := consumerChannel.GetCounterparty().GetChannelID()
	providerConnection := consumerConnection.GetCounterparty()

	consumerClientState, found := k.clientKeeper.GetClientState(ctx, consumerConnection.GetClientID())
	if !found {
		// todo if return err?
		return nil, nil
	}
	providerChainID := consumerClientState.(*ibctm.ClientState).ChainId

	resp := types.QueryProviderInfoResponse{
		ChainID:      providerChainID,
		ClientID:     providerConnection.GetClientID(),
		ConnectionID: providerConnection.GetConnectionID(),
		ChannelID:    providerChannelID,
	}

	return &resp, nil
}
