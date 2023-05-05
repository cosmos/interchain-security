package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/cometbft/cometbft/abci/types"
)

// InitGenesis initializes the CCV consumer state and binds to PortID.
// The three states in which a consumer chain can start/restart:
//
//  1. A client to the provider was never created, i.e. a new consumer chain is started for the first time.
//  2. A consumer chain restarts after a client to the provider was created, but the CCV channel handshake is still in progress
//  3. A consumer chain restarts after the CCV channel handshake was completed.
func (k Keeper) InitGenesis(ctx sdk.Context, state *consumertypes.GenesisState) []abci.ValidatorUpdate {
	// PreCCV is true during the process of a standalone to consumer changeover.
	// At the PreCCV point in the process, the standalone chain has just been upgraded to include
	// the consumer ccv module, but the standalone staking keeper is still managing the validator set.
	// Once the provider validator set starts validating blocks, the consumer CCV module
	// will take over proof of stake capabilities, but the standalone staking keeper will
	// stick around for slashing/jailing purposes.
	if state.PreCCV {
		k.SetPreCCVTrue(ctx)
		k.MarkAsPrevStandaloneChain(ctx)
		k.SetInitialValSet(ctx, state.InitialValSet)
	}
	k.SetInitGenesisHeight(ctx, ctx.BlockHeight()) // Usually 0, but not the case for changeover chains

	k.SetParams(ctx, state.Params)
	// TODO: Remove enabled flag and find a better way to setup integration tests
	// See: https://github.com/cosmos/interchain-security/issues/339
	if !state.Params.Enabled {
		return nil
	}

	k.SetPort(ctx, ccv.ConsumerPortID)

	// Only try to bind to port if it is not already bound, since we may already own
	// port capability from capability InitGenesis
	if !k.IsBound(ctx, ccv.ConsumerPortID) {
		// transfer module binds to the transfer port on InitChain
		// and claims the returned capability
		err := k.BindPort(ctx, ccv.ConsumerPortID)
		if err != nil {
			// If the binding fails, the chain MUST NOT start
			panic(fmt.Sprintf("could not claim port capability: %v", err))
		}
	}

	// initialValSet is checked in NewChain case by ValidateGenesis
	// start a new chain
	if state.NewChain {
		// create the provider client in InitGenesis for new consumer chain. CCV Handshake must be established with this client id.
		clientID, err := k.clientKeeper.CreateClient(ctx, state.ProviderClientState, state.ProviderConsensusState)
		if err != nil {
			// If the client creation fails, the chain MUST NOT start
			panic(err)
		}

		// set provider client id.
		k.SetProviderClientID(ctx, clientID)

		// set default value for valset update ID
		k.SetHeightValsetUpdateID(ctx, uint64(ctx.BlockHeight()), uint64(0))

	} else {
		// chain restarts with the CCV channel established
		if state.ProviderChannelId != "" {
			// set provider channel ID
			k.SetProviderChannel(ctx, state.ProviderChannelId)
			// set all unbonding sequences
			for _, mp := range state.MaturingPackets {
				k.SetPacketMaturityTime(ctx, mp.VscId, mp.MaturityTime)
			}
			// set outstanding downtime slashing requests
			for _, od := range state.OutstandingDowntimeSlashing {
				consAddr, err := sdk.ConsAddressFromBech32(od.ValidatorConsensusAddress)
				if err != nil {
					panic(err)
				}
				k.SetOutstandingDowntime(ctx, consAddr)
			}

			// set last transmission block height
			k.SetLastTransmissionBlockHeight(ctx, state.LastTransmissionBlockHeight)
		}

		// set pending consumer pending packets
		// note that the list includes pending mature VSC packet only if the handshake is completed
		k.AppendPendingPacket(ctx, state.PendingConsumerPackets.List...)

		// set height to valset update id mapping
		for _, h2v := range state.HeightToValsetUpdateId {
			k.SetHeightValsetUpdateID(ctx, h2v.Height, h2v.ValsetUpdateId)
		}

		// set provider client id
		k.SetProviderClientID(ctx, state.ProviderClientId)
	}

	if state.PreCCV {
		return []abci.ValidatorUpdate{}
	}

	// populate cross chain validators states with initial valset
	k.ApplyCCValidatorChanges(ctx, state.InitialValSet)
	return state.InitialValSet
}

// ExportGenesis returns the CCV consumer module's exported genesis
func (k Keeper) ExportGenesis(ctx sdk.Context) (genesis *consumertypes.GenesisState) {
	params := k.GetConsumerParams(ctx)
	if !params.Enabled {
		return consumertypes.DefaultGenesisState()
	}

	// export the current validator set
	valset := k.MustGetCurrentValidatorsAsABCIUpdates(ctx)

	// export all the states created after a provider channel got established
	if channelID, ok := k.GetProviderChannel(ctx); ok {
		clientID, found := k.GetProviderClientID(ctx)
		if !found {
			// This should never happen
			panic("provider client does not exist although provider channel does exist")
		}

		genesis = consumertypes.NewRestartGenesisState(
			clientID,
			channelID,
			k.GetAllPacketMaturityTimes(ctx),
			valset,
			k.GetAllHeightToValsetUpdateIDs(ctx),
			k.GetPendingPackets(ctx),
			k.GetAllOutstandingDowntimes(ctx),
			k.GetLastTransmissionBlockHeight(ctx),
			params,
		)
	} else {
		clientID, ok := k.GetProviderClientID(ctx)
		// if provider clientID and channelID don't exist on the consumer chain,
		// then CCV protocol is disabled for this chain return a default genesis state
		if !ok {
			return consumertypes.DefaultGenesisState()
		}

		// export client states and pending slashing requests into a new chain genesis
		genesis = consumertypes.NewRestartGenesisState(
			clientID,
			"",
			nil,
			valset,
			k.GetAllHeightToValsetUpdateIDs(ctx),
			k.GetPendingPackets(ctx),
			nil,
			consumertypes.LastTransmissionBlockHeight{},
			params,
		)
	}

	return genesis
}
