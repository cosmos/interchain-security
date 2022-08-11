package keeper

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
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

	k.SetValidatorSetUpdateId(ctx, genState.ValsetUpdateId)
	for _, v2h := range genState.ValsetUpdateIdToHeight {
		k.SetValsetUpdateBlockHeight(ctx, v2h.Height, v2h.ValsetUpdateId)
	}

	for _, cccp := range genState.CreateConsumerChainProposals {
		k.SetPendingCreateProposal(ctx, &cccp)
	}
	for _, sccp := range genState.StopConsumerChainProposals {
		k.SetPendingStopProposal(ctx, sccp.ChainId, sccp.StopTime)
	}
	for _, ubdOp := range genState.UnbondingOps {
		k.SetUnbondingOp(ctx, ubdOp)
	}

	// Set initial state for each consumer chain
	for _, cs := range genState.ConsumerStates {
		chainID := cs.ChainId
		k.SetConsumerClientId(ctx, chainID, cs.ClientId)
		k.SetConsumerGenesis(ctx, chainID, cs.ConsumerGenesis)
		if cs.LockUnbondingOnTimeout {
			k.SetLockUnbondingOnTimeout(ctx, chainID)
		}

		if cs.ChannelId == "" {
			for _, vsc := range cs.PendingValsetChanges {
				k.AppendPendingVSC(ctx, chainID, vsc)
			}
		} else {
			k.SetChannelToChain(ctx, cs.ChannelId, chainID)
			k.SetChainToChannel(ctx, chainID, cs.ChannelId)
			k.SetInitChainHeight(ctx, chainID, cs.InitialHeight)

			k.SetSlashAcks(ctx, cs.ChainId, cs.SlashDowntimeAck)
			for _, ubdOpIndex := range cs.UnbondingOpsIndex {
				k.SetUnbondingOpIndex(ctx, chainID, ubdOpIndex.ValsetUpdateId, ubdOpIndex.UnbondingOpIndex)
			}
		}
	}

	k.SetParams(ctx, genState.Params)
}

func (k Keeper) ExportGenesis(ctx sdk.Context) *types.GenesisState {
	var consumerStates []types.ConsumerState
	// export states for each consumer chains
	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID, clientID string) bool {
		gen, found := k.GetConsumerGenesis(ctx, chainID)
		if !found {
			panic(fmt.Errorf("cannot find genesis for consumer chain %s with client %s", chainID, clientID))
		}

		cs := types.ConsumerState{
			ChainId:                chainID,
			ClientId:               clientID,
			ConsumerGenesis:        gen,
			LockUnbondingOnTimeout: k.GetLockUnbondingOnTimeout(ctx, chainID),
		}

		// try to find channel id for the current consumer chain
		channelId, found := k.GetChainToChannel(ctx, chainID)
		if found {
			cs.ChannelId = channelId
			cs.InitialHeight = k.GetInitChainHeight(ctx, chainID)
			cs.SlashDowntimeAck = k.GetSlashAcks(ctx, chainID)
			ubdOpIndexes := []types.UnbondingOpIndex{}
			k.IterateOverUnbondingOpIndex(ctx, chainID, func(vscID uint64, ubdIndex []uint64) bool {
				ubdOpIndexes = append(ubdOpIndexes, types.UnbondingOpIndex{ValsetUpdateId: vscID, UnbondingOpIndex: ubdIndex})
				return true
			})
			cs.UnbondingOpsIndex = ubdOpIndexes
		} else {
			if pendingVSC, found := k.GetPendingVSCs(ctx, chainID); found {
				cs.PendingValsetChanges = pendingVSC
			}
		}

		consumerStates = append(consumerStates, cs)
		return true
	})

	// export provider chain states
	vscID := k.GetValidatorSetUpdateId(ctx)
	vscIDToHeights := []types.ValsetUpdateIdToHeight{}
	k.IterateValsetUpdateBlockHeight(ctx, func(vscID, height uint64) bool {
		vscIDToHeights = append(vscIDToHeights, types.ValsetUpdateIdToHeight{ValsetUpdateId: vscID, Height: height})
		return true
	})

	ubdOps := []ccv.UnbondingOp{}
	k.IterateOverUnbondingOps(ctx, func(id uint64, ubdOp ccv.UnbondingOp) bool {
		ubdOps = append(ubdOps, ubdOp)
		return true
	})

	stopChainProposals := []types.StopConsumerChainProposal{}
	k.IteratePendingStopProposal(ctx, func(chainID string, stopTime time.Time) bool {
		stopChainProposals = append(stopChainProposals,
			types.StopConsumerChainProposal{
				ChainId:  chainID,
				StopTime: stopTime,
			},
		)
		return true
	})
	createConsumerChainProposals := []types.CreateConsumerChainProposal{}
	k.IteratePendingCreateProposal(ctx, func(clientInfo types.CreateConsumerChainProposal) bool {
		createConsumerChainProposals = append(createConsumerChainProposals, clientInfo)
		return true
	})

	params := k.GetParams(ctx)

	return types.NewGenesisState(
		vscID,
		vscIDToHeights,
		consumerStates,
		ubdOps,
		createConsumerChainProposals,
		stopChainProposals,
		params,
	)
}
