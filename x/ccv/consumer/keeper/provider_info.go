package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctm "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

func (k Keeper) GetProviderChainInfo(ctx sdk.Context) (*types.QueryProviderInfoResponse, error) {
	consumerChannelID, found := k.GetProviderChannel(ctx)
	consumerChannel, _ := k.channelKeeper.GetChannel(ctx, ccvtypes.ConsumerPortID, consumerChannelID)
	providerChannelID := consumerChannel.GetCounterparty().GetChannelID()

	_, consumerConnection, err := k.connectionKeeper.GetChannelConnection(ctx, ccvtypes.ConsumerPortID, consumerChannelID)
	if err != nil {
		return nil, err
	}

	providerConnection := consumerConnection.GetCounterparty()

	providerClientState, found := k.clientKeeper.GetClientState(ctx, providerConnection.GetClientID())
	if !found {
		// todo if return err?
		return nil, nil
	}
	providerChainID := providerClientState.(*ibctm.ClientState).ChainId

	resp := types.QueryProviderInfoResponse{
		ChainID:      providerChainID,
		ClientID:     providerConnection.GetClientID(),
		ConnectionID: providerConnection.GetConnectionID(),
		ChannelID:    providerChannelID,
	}

	return &resp, nil
}
