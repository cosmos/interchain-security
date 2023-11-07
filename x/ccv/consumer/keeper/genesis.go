package keeper

import (
	"context"
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"

	abci "github.com/cometbft/cometbft/abci/types"

	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// InitGenesis initializes the CCV consumer state and binds to PortID.
// The three states in which a consumer chain can start/restart:
//
//  1. A client to the provider was never created, i.e. a new consumer chain is started for the first time.
//  2. A consumer chain restarts after a client to the provider was created, but the CCV channel handshake is still in progress
//  3. A consumer chain restarts after the CCV channel handshake was completed.
func (k Keeper) InitGenesis(ctx context.Context, state *ccv.GenesisState) []abci.ValidatorUpdate {
	sdkCtx := sdk.UnwrapSDKContext(ctx)
	// PreCCV is true during the process of a standalone to consumer changeover.
	// At the PreCCV point in the process, the standalone chain has just been upgraded to include
	// the consumer ccv module, but the standalone staking keeper is still managing the validator set.
	// Once the provider validator set starts validating blocks, the consumer CCV module
	// will take over proof of stake capabilities, but the standalone staking keeper will
	// stick around for slashing/jailing purposes.
	if state.PreCCV {
		k.SetPreCCVTrue(sdkCtx)
		k.MarkAsPrevStandaloneChain(sdkCtx)
		k.SetInitialValSet(sdkCtx, state.InitialValSet)
	}
	k.SetInitGenesisHeight(sdkCtx, sdkCtx.BlockHeight()) // Usually 0, but not the case for changeover chains

	k.SetParams(sdkCtx, state.Params)
	// TODO: Remove enabled flag and find a better way to setup integration tests
	// See: https://github.com/cosmos/interchain-security/issues/339
	if !state.Params.Enabled {
		return nil
	}

	k.SetPort(sdkCtx, ccv.ConsumerPortID)

	// Only try to bind to port if it is not already bound, since we may already own
	// port capability from capability InitGenesis
	if !k.IsBound(sdkCtx, ccv.ConsumerPortID) {
		// transfer module binds to the transfer port on InitChain
		// and claims the returned capability
		err := k.BindPort(sdkCtx, ccv.ConsumerPortID)
		if err != nil {
			// If the binding fails, the chain MUST NOT start
			panic(fmt.Sprintf("could not claim port capability: %v", err))
		}
	}

	// initialValSet is checked in NewChain case by ValidateGenesis
	// start a new chain
	if state.NewChain {
		// create the provider client in InitGenesis for new consumer chain. CCV Handshake must be established with this client id.
		clientID, err := k.clientKeeper.CreateClient(sdkCtx, state.ProviderClientState, state.ProviderConsensusState)
		if err != nil {
			// If the client creation fails, the chain MUST NOT start
			panic(err)
		}

		// set provider client id.
		k.SetProviderClientID(sdkCtx, clientID)

		// set default value for valset update ID
		k.SetHeightValsetUpdateID(sdkCtx, uint64(sdkCtx.BlockHeight()), uint64(0))

	} else {
		// chain restarts with the CCV channel established
		if state.ProviderChannelId != "" {
			// set provider channel ID
			k.SetProviderChannel(sdkCtx, state.ProviderChannelId)
			// set all unbonding sequences
			for _, mp := range state.MaturingPackets {
				k.SetPacketMaturityTime(sdkCtx, mp.VscId, mp.MaturityTime)
			}
			// set outstanding downtime slashing requests
			for _, od := range state.OutstandingDowntimeSlashing {
				consAddr, err := sdk.ConsAddressFromBech32(od.ValidatorConsensusAddress)
				if err != nil {
					panic(err)
				}
				k.SetOutstandingDowntime(sdkCtx, consAddr)
			}

			// set last transmission block height
			k.SetLastTransmissionBlockHeight(sdkCtx, state.LastTransmissionBlockHeight)
		}

		// Set pending consumer packets, using the depreciated ConsumerPacketDataList type
		// that exists for genesis.
		// note that the list includes pending mature VSC packet only if the handshake is completed
		for _, packet := range state.PendingConsumerPackets.List {
			k.AppendPendingPacket(sdkCtx, packet.Type, packet.Data)
		}

		// set height to valset update id mapping
		for _, h2v := range state.HeightToValsetUpdateId {
			k.SetHeightValsetUpdateID(sdkCtx, h2v.Height, h2v.ValsetUpdateId)
		}

		// set provider client id
		k.SetProviderClientID(sdkCtx, state.ProviderClientId)
	}

	if state.PreCCV {
		return []abci.ValidatorUpdate{}
	}

	// populate cross chain validators states with initial valset
	k.ApplyCCValidatorChanges(sdkCtx, state.InitialValSet)
	return state.InitialValSet
}

// ExportGenesis returns the CCV consumer module's exported genesis
func (k Keeper) ExportGenesis(ctx context.Context) (genesis *ccv.GenesisState) {
	sdkCtx := sdk.UnwrapSDKContext(ctx)
	params := k.GetConsumerParams(sdkCtx)
	if !params.Enabled {
		return ccv.DefaultGenesisState()
	}

	// export the current validator set
	valset := k.MustGetCurrentValidatorsAsABCIUpdates(sdkCtx)

	// export pending packets using the depreciated ConsumerPacketDataList type
	pendingPackets := k.GetPendingPackets(sdkCtx)
	pendingPacketsDepreciated := ccv.ConsumerPacketDataList{}
	pendingPacketsDepreciated.List = append(pendingPacketsDepreciated.List, pendingPackets...)

	// export all the states created after a provider channel got established
	if channelID, ok := k.GetProviderChannel(sdkCtx); ok {
		clientID, found := k.GetProviderClientID(sdkCtx)
		if !found {
			// This should never happen
			panic("provider client does not exist although provider channel does exist")
		}

		genesis = ccv.NewRestartGenesisState(
			clientID,
			channelID,
			k.GetAllPacketMaturityTimes(sdkCtx),
			valset,
			k.GetAllHeightToValsetUpdateIDs(sdkCtx),
			pendingPacketsDepreciated,
			k.GetAllOutstandingDowntimes(sdkCtx),
			k.GetLastTransmissionBlockHeight(sdkCtx),
			params,
		)
	} else {
		clientID, ok := k.GetProviderClientID(sdkCtx)
		// if provider clientID and channelID don't exist on the consumer chain,
		// then CCV protocol is disabled for this chain return a default genesis state
		if !ok {
			return ccv.DefaultGenesisState()
		}

		// export client states and pending slashing requests into a new chain genesis
		genesis = ccv.NewRestartGenesisState(
			clientID,
			"",
			nil,
			valset,
			k.GetAllHeightToValsetUpdateIDs(sdkCtx),
			pendingPacketsDepreciated,
			nil,
			ccv.LastTransmissionBlockHeight{},
			params,
		)
	}

	return genesis
}
