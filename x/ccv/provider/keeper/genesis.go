package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	ccv "github.com/cosmos/interchain-security/x/types"
)

// InitGenesis initializes the CCV provider state and binds to PortID.
func (k Keeper) InitGenesis(ctx sdk.Context, genState *ccv.ProviderGenesisState) {
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
	for _, ubdOp := range genState.UnbondingOps {
		k.SetUnbondingOp(ctx, ubdOp)
	}

	// Note that MatureUnbondingOps aren't stored across blocks, but it
	// might be used after implementing standalone to consumer transition
	if genState.MatureUnbondingOps != nil {
		k.AppendMaturedUnbondingOps(ctx, genState.MatureUnbondingOps.Ids)
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
		for _, ubdOpIndex := range cs.UnbondingOpsIndex {
			k.SetUnbondingOpIndex(ctx, chainID, ubdOpIndex.GetVscId(), ubdOpIndex.GetUnbondingOpIds())
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
		k.SetValidatorConsumerPubKey(ctx, item.ChainId, *item.ProviderAddr, *item.ConsumerKey)
	}

	for _, item := range genState.ValidatorsByConsumerAddr {
		k.SetValidatorByConsumerAddr(ctx, item.ChainId, *item.ConsumerAddr, *item.ProviderAddr)
	}

	for _, item := range genState.ConsumerAddrsToPrune {
		for _, addr := range item.ConsumerAddrs.Addresses {
			k.AppendConsumerAddrsToPrune(ctx, item.ChainId, item.VscId, *addr)
		}
	}

	k.SetParams(ctx, genState.Params)
	k.InitializeSlashMeter(ctx)
}

// ExportGenesis returns the CCV provider module's exported genesis
func (k Keeper) ExportGenesis(ctx sdk.Context) *ccv.ProviderGenesisState {
	// get a list of all registered consumer chains
	registeredChains := k.GetAllConsumerChains(ctx)

	// export states for each consumer chains
	var consumerStates []ccv.ConsumerState
	for _, chain := range registeredChains {
		gen, found := k.GetConsumerGenesis(ctx, chain.ChainId)
		if !found {
			panic(fmt.Errorf("cannot find genesis for consumer chain %s with client %s", chain.ChainId, chain.ClientId))
		}

		// initial consumer chain states
		cs := ccv.ConsumerState{
			ChainId:           chain.ChainId,
			ClientId:          chain.ClientId,
			ConsumerGenesis:   gen,
			UnbondingOpsIndex: k.GetAllUnbondingOpIndexes(ctx, chain.ChainId),
		}

		// try to find channel id for the current consumer chain
		channelId, found := k.GetChainToChannel(ctx, chain.ChainId)
		if found {
			cs.ChannelId = channelId
			cs.InitialHeight, found = k.GetInitChainHeight(ctx, chain.ChainId)
			if !found {
				panic(fmt.Errorf("cannot find init height for consumer chain %s", chain.ChainId))
			}
			cs.SlashDowntimeAck = k.GetSlashAcks(ctx, chain.ChainId)
		}

		cs.PendingValsetChanges = k.GetPendingVSCPackets(ctx, chain.ChainId)
		consumerStates = append(consumerStates, cs)

	}

	// ConsumerAddrsToPrune are added only for registered consumer chains
	consumerAddrsToPrune := []ccv.ConsumerAddrsToPrune{}
	for _, chain := range registeredChains {
		consumerAddrsToPrune = append(consumerAddrsToPrune, k.GetAllConsumerAddrsToPrune(ctx, chain.ChainId)...)
	}

	params := k.GetParams(ctx)

	return ccv.NewProviderGenesisState(
		k.GetValidatorSetUpdateId(ctx),
		k.GetAllValsetUpdateBlockHeights(ctx),
		consumerStates,
		k.GetAllUnbondingOps(ctx),
		&ccv.MaturedUnbondingOps{Ids: k.GetMaturedUnbondingOps(ctx)},
		k.GetAllPendingConsumerAdditionProps(ctx),
		k.GetAllPendingConsumerRemovalProps(ctx),
		params,
		k.GetAllValidatorConsumerPubKeys(ctx, nil),
		k.GetAllValidatorsByConsumerAddr(ctx, nil),
		consumerAddrsToPrune,
	)
}
