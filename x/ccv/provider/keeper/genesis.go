package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func (k Keeper) InitGenesis(ctx sdk.Context, genState *types.GenesisState) {
	k.SetPort(ctx, providertypes.PortID)

	// Only try to bind to port if it is not already bound, since we may already own
	// port capability from capability InitGenesis
	if !k.IsBound(ctx, providertypes.PortID) {
		// transfer module binds to the transfer port on InitChain
		// and claims the returned capability
		err := k.BindPort(ctx, providertypes.PortID)
		if err != nil {
			panic(fmt.Sprintf("could not claim port capability: %v", err))
		}
	}

	// Set initial state for each consumer chain
	for _, cc := range genState.ConsumerStates {
		k.SetChainToChannel(ctx, cc.ChainId, cc.ChannelId)
		k.SetChannelToChain(ctx, cc.ChannelId, cc.ChainId)
	}

	k.SetParams(ctx, genState.Params)
}

func (k Keeper) ExportGenesis(ctx sdk.Context) *types.GenesisState {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, types.ChannelToChainPrefix())
	defer iterator.Close()

	if !iterator.Valid() {
		return types.DefaultGenesisState()
	}

	var consumerStates []types.ConsumerState

	for ; iterator.Valid(); iterator.Next() {
		channelID := string(iterator.Key()[len(types.ChannelToChainPrefix()):])
		chainID := string(iterator.Value())

		cc := types.ConsumerState{
			ChainId:   chainID,
			ChannelId: channelID,
		}
		consumerStates = append(consumerStates, cc)
	}

	params := k.GetParams(ctx)

	return types.NewGenesisState(consumerStates, params)
}
