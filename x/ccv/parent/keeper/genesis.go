package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/parent/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
)

func (k Keeper) InitGenesis(ctx sdk.Context, genState *types.GenesisState) {
	k.SetPort(ctx, parenttypes.PortID)

	// Only try to bind to port if it is not already bound, since we may already own
	// port capability from capability InitGenesis
	if !k.IsBound(ctx, parenttypes.PortID) {
		// transfer module binds to the transfer port on InitChain
		// and claims the returned capability
		err := k.BindPort(ctx, parenttypes.PortID)
		if err != nil {
			panic(fmt.Sprintf("could not claim port capability: %v", err))
		}
	}

	// Set initial state for each child chain
	for _, cc := range genState.ChildStates {
		k.SetChainToChannel(ctx, cc.ChainId, cc.ChannelId)
		k.SetChannelToChain(ctx, cc.ChannelId, cc.ChainId)
		k.SetChannelStatus(ctx, cc.ChannelId, cc.Status)
	}

	k.SetParams(ctx, genState.Params)
}

func (k Keeper) ExportGenesis(ctx sdk.Context) *types.GenesisState {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte(parenttypes.ChannelToChainKeyPrefix+"/"))
	defer iterator.Close()

	if !iterator.Valid() {
		return types.DefaultGenesisState()
	}

	var childStates []types.ChildState

	for ; iterator.Valid(); iterator.Next() {
		channelID := string(iterator.Key()[len(parenttypes.ChannelToChainKeyPrefix+"/"):])
		chainID := string(iterator.Value())

		status := k.GetChannelStatus(ctx, channelID)
		cc := types.ChildState{
			ChainId:   chainID,
			ChannelId: channelID,
			Status:    status,
		}
		childStates = append(childStates, cc)
	}

	params := k.GetParams(ctx)

	return types.NewGenesisState(childStates, params)
}
