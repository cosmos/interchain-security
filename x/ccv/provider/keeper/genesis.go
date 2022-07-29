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

	// Set initial state for each consumer chain
	for _, cc := range genState.ConsumerStates {
		k.SetChainToChannel(ctx, cc.ChainId, cc.ChannelId)
		k.SetChannelToChain(ctx, cc.ChannelId, cc.ChainId)
	}

	k.SetParams(ctx, genState.Params)
}

func (k Keeper) ExportGenesis(ctx sdk.Context) *types.GenesisState {
	var consumerStates []types.ConsumerState

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
				id := types.UnbondingOpIndexKey(chainID, vscID)
				ubdOpIndexes = append(ubdOpIndexes, types.UnbondingOpIndex{Id: id, UnbondingOpIndex: ubdIndex})
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

	// export provider states
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

	k.IterateValsetUpdateBlockHeight(ctx, func(vscID, height uint64) bool {
		vscIDToHeights = append(vscIDToHeights, types.ValsetUpdateIdToHeight{ValsetUpdateId: vscID, Height: height})
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
