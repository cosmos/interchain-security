package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
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
			panic(fmt.Sprintf("could not claim port capability: %v", err))
		}
	}

	k.SetValidatorSetUpdateId(ctx, genState.ValsetUpdateId)
	for _, v2h := range genState.ValsetUpdateIdToHeight {
		k.SetValsetUpdateBlockHeight(ctx, v2h.ValsetUpdateId, v2h.Height)
	}

	for _, prop := range genState.ConsumerAdditionProposals {
		// prevent implicit memory aliasing
		prop := prop
		if err := k.SetPendingConsumerAdditionProp(ctx, &prop); err != nil {
			panic(fmt.Errorf("pending create consumer chain proposal could not be persisted: %w", err))
		}
	}
	for _, prop := range genState.ConsumerRemovalProposals {
		k.SetPendingConsumerRemovalProp(ctx, prop.ChainId, prop.StopTime)
	}
	for _, ubdOp := range genState.UnbondingOps {
		k.SetUnbondingOp(ctx, ubdOp)
	}

	// Note that MatureUnbondingOps aren't stored across blocks, but it
	// might be used after implementing sovereign to consumer transition
	if genState.MatureUnbondingOps != nil {
		k.AppendMaturedUnbondingOps(ctx, genState.MatureUnbondingOps.Ids)
	}

	// Set initial state for each consumer chain
	for _, cs := range genState.ConsumerStates {
		chainID := cs.ChainId
		k.SetConsumerClientId(ctx, chainID, cs.ClientId)
		if err := k.SetConsumerGenesis(ctx, chainID, cs.ConsumerGenesis); err != nil {
			panic(fmt.Errorf("consumer chain genesis could not be persisted: %w", err))
		}
		// check if the CCV channel was established
		if cs.ChannelId != "" {
			k.SetChannelToChain(ctx, cs.ChannelId, chainID)
			k.SetChainToChannel(ctx, chainID, cs.ChannelId)
			k.SetInitChainHeight(ctx, chainID, cs.InitialHeight)

			k.SetSlashAcks(ctx, cs.ChainId, cs.SlashDowntimeAck)
			for _, ubdOpIndex := range cs.UnbondingOpsIndex {
				k.SetUnbondingOpIndex(ctx, chainID, ubdOpIndex.ValsetUpdateId, ubdOpIndex.UnbondingOpIndex)
			}
		} else {
			k.AppendPendingVSCPackets(ctx, chainID, cs.PendingValsetChanges...)
		}
	}

	// Import key assignment state
	for _, item := range genState.ValidatorConsumerPubkeys {
		k.SetValidatorConsumerPubKey(ctx, item.ChainId, item.ProviderAddr, *item.ConsumerKey)
	}

	for _, item := range genState.ValidatorsByConsumerAddr {
		k.SetValidatorByConsumerAddr(ctx, item.ChainId, item.ConsumerAddr, item.ProviderAddr)
	}

	for _, item := range genState.ConsumerAddrsToPrune {
		for _, addr := range item.ConsumerAddrs.Addresses {
			k.AppendConsumerAddrsToPrune(ctx, item.ChainId, item.VscId, addr)
		}
	}

	k.SetParams(ctx, genState.Params)
}

// ExportGenesis returns the CCV provider module's exported genesis
func (k Keeper) ExportGenesis(ctx sdk.Context) *types.GenesisState {
	var consumerStates []types.ConsumerState
	// export states for each consumer chains
	for _, chain := range k.IterateConsumerChains(ctx) {
		gen, found := k.GetConsumerGenesis(ctx, chain.ChainId)
		if !found {
			panic(fmt.Errorf("cannot find genesis for consumer chain %s with client %s", chain.ChainId, chain.ClientId))
		}

		// initial consumer chain states
		cs := types.ConsumerState{
			ChainId:         chain.ChainId,
			ClientId:        chain.ClientId,
			ConsumerGenesis: gen,
		}

		// try to find channel id for the current consumer chain
		channelId, found := k.GetChainToChannel(ctx, chain.ChainId)
		if found {
			cs.ChannelId = channelId
			cs.InitialHeight, found = k.GetInitChainHeight(ctx, chain.ChainId)
			if !found {
				panic(fmt.Errorf("cannot find genesis for consumer chain %s with client %s", chain.ChainId, chain.ClientId))
			}
			cs.SlashDowntimeAck = k.GetSlashAcks(ctx, chain.ChainId)
			for _, unbondingOpsIndex := range k.IterateOverUnbondingOpIndex(ctx, chain.ChainId) {
				cs.UnbondingOpsIndex = append(cs.UnbondingOpsIndex,
					types.UnbondingOpIndex{ValsetUpdateId: unbondingOpsIndex.VscId, UnbondingOpIndex: unbondingOpsIndex.UnbondingOpIds},
				)
			}
		}

		cs.PendingValsetChanges = k.GetPendingVSCPackets(ctx, chain.ChainId)
		consumerStates = append(consumerStates, cs)

	}

	// export provider chain state
	vscID := k.GetValidatorSetUpdateId(ctx)
	vscIDToHeights := k.IterateValsetUpdateBlockHeight(ctx)

	ubdOps := k.IterateOverUnbondingOps(ctx)

	matureUbdOps, err := k.GetMaturedUnbondingOps(ctx)
	if err != nil {
		panic(err)
	}

	addProps := k.IteratePendingConsumerAdditionProps(ctx)

	remProps := k.IteratePendingConsumerRemovalProps(ctx)

	// Export key assignment states
	validatorConsumerPubKeys := k.IterateAllValidatorConsumerPubKeys(ctx)

	validatorsByConsumerAddr := k.IterateAllValidatorsByConsumerAddr(ctx)

	consumerAddrsToPrune := []types.ConsumerAddrsToPrune{}
	// ConsumerAddrsToPrune are added only for registered consumer chains
	for _, chain := range k.IterateConsumerChains(ctx) {
		consumerAddrsToPrune = append(consumerAddrsToPrune, k.IterateConsumerAddrsToPrune(ctx, chain.ChainId)...)
	}

	params := k.GetParams(ctx)

	return types.NewGenesisState(
		vscID,
		vscIDToHeights,
		consumerStates,
		ubdOps,
		&ccv.MaturedUnbondingOps{Ids: matureUbdOps},
		addProps,
		remProps,
		params,
		validatorConsumerPubKeys,
		validatorsByConsumerAddr,
		consumerAddrsToPrune,
	)
}
