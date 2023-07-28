package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctm "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
)

func (k Keeper) GetProviderChainInfo(ctx sdk.Context) (*types.QueryProviderInfoResponse, error) {
	providerClientID, found := k.GetProviderClientID(ctx)
	if !found {
		return nil, nil
	}
	clientState, found := k.clientKeeper.GetClientState(ctx, providerClientID)
	if !found {
		return nil, nil
	}
	providerChainID := clientState.(*ibctm.ClientState).ChainId
	resp := types.QueryProviderInfoResponse{
		ChainID: providerChainID,
	}

	return &resp, nil
}
