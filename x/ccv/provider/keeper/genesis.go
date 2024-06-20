package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

// InitGenesis initializes the CCV provider state and binds to PortID.
func (k Keeper) InitGenesis(ctx sdk.Context, genState *types.GenesisState) {
	k.SetPort(ctx, ccv.ProviderPortID)

	// Only try to bind to port if it is not already bound, since we may already own
	// port capability from capability InitGenesis
	if !k.IsBound(ctx, ccv.ProviderPortID) {
		// CCV module binds to the provider port on InitChain
		// and claims the returned capability
		err := k.BindPort(ctx, ccv.ProviderPortID)
		if err != nil {
			// If the binding fails, the chain MUST NOT start
			panic(fmt.Errorf("could not claim port capability: %v", err))
		}
	}

	k.SetValidatorSetUpdateId(ctx, genState.ValsetUpdateId)
	for _, v2h := range genState.ValsetUpdateIdToHeight {
		k.SetValsetUpdateBlockHeight(ctx, v2h.ValsetUpdateId, v2h.Height)
	}

	for _, prop := range genState.ConsumerAdditionProposals {
		// prevent implicit memory aliasing
		p := prop
		k.SetPendingConsumerAdditionProp(ctx, &p)
	}
	for _, prop := range genState.ConsumerRemovalProposals {
		p := prop
		k.SetPendingConsumerRemovalProp(ctx, &p)
	}

	// Set initial state for each consumer chain
	for _, cs := range genState.ConsumerStates {
		chainID := cs.ChainId
		k.SetConsumerClientId(ctx, chainID, cs.ClientId)
		if err := k.SetConsumerGenesis(ctx, chainID, cs.ConsumerGenesis); err != nil {
			// An error here would indicate something is very wrong,
			// the ConsumerGenesis validated in ConsumerState.Validate().
			panic(fmt.Errorf("consumer chain genesis could not be persisted: %w", err))
		}
		// check if the CCV channel was established
		if cs.ChannelId != "" {
			k.SetChannelToChain(ctx, cs.ChannelId, chainID)
			k.SetChainToChannel(ctx, chainID, cs.ChannelId)
			k.SetInitChainHeight(ctx, chainID, cs.InitialHeight)
			k.SetSlashAcks(ctx, cs.ChainId, cs.SlashDowntimeAck)
		} else {
			k.AppendPendingVSCPackets(ctx, chainID, cs.PendingValsetChanges...)
		}
	}

	// Import key assignment state
	for _, item := range genState.ValidatorConsumerPubkeys {
		providerAddr := types.NewProviderConsAddress(item.ProviderAddr)
		k.SetValidatorConsumerPubKey(ctx, item.ChainId, providerAddr, *item.ConsumerKey)
	}

	for _, item := range genState.ValidatorsByConsumerAddr {
		consumerAddr := types.NewConsumerConsAddress(item.ConsumerAddr)
		providerAddr := types.NewProviderConsAddress(item.ProviderAddr)
		k.SetValidatorByConsumerAddr(ctx, item.ChainId, consumerAddr, providerAddr)
	}

	for _, item := range genState.ConsumerAddrsToPruneV2 {
		for _, addr := range item.ConsumerAddrs.Addresses {
			consumerAddr := types.NewConsumerConsAddress(addr)
			k.AppendConsumerAddrsToPruneV2(ctx, item.ChainId, item.PruneAfterTs, consumerAddr)
		}
	}

	for _, item := range genState.InitTimeoutTimestamps {
		k.SetInitTimeoutTimestamp(ctx, item.ChainId, item.Timestamp)
	}

	k.SetParams(ctx, genState.Params)
	k.InitializeSlashMeter(ctx)
}

// ExportGenesis returns the CCV provider module's exported genesis
func (k Keeper) ExportGenesis(ctx sdk.Context) *types.GenesisState {
	// get a list of all registered consumer chains
	registeredChainIDs := k.GetAllRegisteredConsumerChainIDs(ctx)

	// export states for each consumer chains
	var consumerStates []types.ConsumerState
	for _, chainID := range registeredChainIDs {
		// no need for the second return value of GetConsumerClientId
		// as GetAllRegisteredConsumerChainIDs already iterated through
		// the entire prefix range
		clientID, _ := k.GetConsumerClientId(ctx, chainID)
		gen, found := k.GetConsumerGenesis(ctx, chainID)
		if !found {
			panic(fmt.Errorf("cannot find genesis for consumer chain %s with client %s", chainID, clientID))
		}

		// initial consumer chain states
		cs := types.ConsumerState{
			ChainId:         chainID,
			ClientId:        clientID,
			ConsumerGenesis: gen,
		}

		// try to find channel id for the current consumer chain
		channelId, found := k.GetChainToChannel(ctx, chainID)
		if found {
			cs.ChannelId = channelId
			cs.InitialHeight, found = k.GetInitChainHeight(ctx, chainID)
			if !found {
				panic(fmt.Errorf("cannot find init height for consumer chain %s", chainID))
			}
			cs.SlashDowntimeAck = k.GetSlashAcks(ctx, chainID)
		}

		cs.PendingValsetChanges = k.GetPendingVSCPackets(ctx, chainID)
		consumerStates = append(consumerStates, cs)
	}

	// ConsumerAddrsToPrune are added only for registered consumer chains
	consumerAddrsToPrune := []types.ConsumerAddrsToPruneV2{}
	for _, chainID := range registeredChainIDs {
		consumerAddrsToPrune = append(consumerAddrsToPrune, k.GetAllConsumerAddrsToPruneV2(ctx, chainID)...)
	}

	params := k.GetParams(ctx)

	return types.NewGenesisState(
		k.GetValidatorSetUpdateId(ctx),
		k.GetAllValsetUpdateBlockHeights(ctx),
		consumerStates,
		k.GetAllPendingConsumerAdditionProps(ctx),
		k.GetAllPendingConsumerRemovalProps(ctx),
		params,
		k.GetAllValidatorConsumerPubKeys(ctx, nil),
		k.GetAllValidatorsByConsumerAddr(ctx, nil),
		consumerAddrsToPrune,
		k.GetAllInitTimeoutTimestamps(ctx),
	)
}
