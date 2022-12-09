package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	tmcrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
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
		k.SetPendingConsumerRemovalProp(ctx, &prop)
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
			k.AppendPendingPackets(ctx, chainID, cs.PendingValsetChanges...)
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
	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID, clientID string) (stop bool) {
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
				panic(fmt.Errorf("cannot find genesis for consumer chain %s with client %s", chainID, clientID))
			}
			cs.SlashDowntimeAck = k.GetSlashAcks(ctx, chainID)
			k.IterateUnbondingOpIndex(ctx, chainID, func(vscID uint64, ubdIndex []uint64) (stop bool) {
				cs.UnbondingOpsIndex = append(cs.UnbondingOpsIndex,
					types.UnbondingOpIndex{ValsetUpdateId: vscID, UnbondingOpIndex: ubdIndex},
				)
				return false // do not stop the iteration
			})
		}

		cs.PendingValsetChanges = k.GetPendingPackets(ctx, chainID)
		consumerStates = append(consumerStates, cs)
		return false // do not stop the iteration
	})

	// export provider chain state
	vscID := k.GetValidatorSetUpdateId(ctx)
	vscIDToHeights := []types.ValsetUpdateIdToHeight{}
	k.IterateValsetUpdateBlockHeight(ctx, func(vscID, height uint64) (stop bool) {
		vscIDToHeights = append(vscIDToHeights, types.ValsetUpdateIdToHeight{ValsetUpdateId: vscID, Height: height})
		return false // do not stop the iteration
	})

	ubdOps := []ccv.UnbondingOp{}
	k.IterateUnbondingOps(ctx, func(id uint64, ubdOp ccv.UnbondingOp) (stop bool) {
		ubdOps = append(ubdOps, ubdOp)
		return false // do not stop the iteration
	})

	matureUbdOps, err := k.GetMaturedUnbondingOps(ctx)
	if err != nil {
		panic(err)
	}

	addProps := []types.ConsumerAdditionProposal{}
	k.IteratePendingConsumerAdditionProps(ctx, func(prop types.ConsumerAdditionProposal) (stop bool) {
		addProps = append(addProps, prop)
		return false // do not stop the iteration
	})

	remProps := []types.ConsumerRemovalProposal{}
	k.IteratePendingConsumerRemovalProps(ctx, func(prop types.ConsumerRemovalProposal) (stop bool) {
		remProps = append(remProps, prop)
		return false // do not stop the iteration
	})

	// Export key assignment states
	validatorConsumerPubKeys := []types.ValidatorConsumerPubKey{}
	k.IterateAllValidatorConsumerPubKeys(ctx, func(chainID string, providerAddr sdk.ConsAddress, consumerKey tmcrypto.PublicKey) (stop bool) {
		validatorConsumerPubKeys = append(validatorConsumerPubKeys, types.ValidatorConsumerPubKey{
			ChainId:      chainID,
			ProviderAddr: providerAddr,
			ConsumerKey:  &consumerKey,
		})
		return false // do not stop the iteration
	})

	validatorsByConsumerAddr := []types.ValidatorByConsumerAddr{}
	k.IterateAllValidatorsByConsumerAddr(ctx, func(chainID string, consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		validatorsByConsumerAddr = append(validatorsByConsumerAddr, types.ValidatorByConsumerAddr{
			ChainId:      chainID,
			ConsumerAddr: consumerAddr,
			ProviderAddr: providerAddr,
		})
		return false // do not stop the iteration
	})

	consumerAddrsToPrune := []types.ConsumerAddrsToPrune{}
	// ConsumerAddrsToPrune are added only for registered consumer chains
	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID string, _ string) (stopOuter bool) {
		k.IterateConsumerAddrsToPrune(ctx, chainID, func(vscID uint64, consumerAddrs types.AddressList) (stopInner bool) {
			consumerAddrsToPrune = append(consumerAddrsToPrune, types.ConsumerAddrsToPrune{
				ChainId:       chainID,
				VscId:         vscID,
				ConsumerAddrs: &consumerAddrs,
			})
			return false // do not stop the iteration
		})
		return false // do not stop the iteration
	})

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
