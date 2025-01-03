package keeper

import (
	"fmt"

	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	conntypes "github.com/cosmos/ibc-go/v8/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

// InitGenesis initializes the CCV consumer state and binds to PortID.
// The three states in which a consumer chain can start/restart:
//
//  1. A client to the provider was never created, i.e. a new consumer chain is started for the first time.
//  2. A consumer chain restarts after a client to the provider was created, but the CCV channel handshake is still in progress
//  3. A consumer chain restarts after the CCV channel handshake was completed.
func (k Keeper) InitGenesis(ctx sdk.Context, state *types.GenesisState) []abci.ValidatorUpdate {
	// PreCCV is true during the process of a standalone to consumer changeover.
	// At the PreCCV point in the process, the standalone chain has just been upgraded to include
	// the consumer ccv module, but the standalone staking keeper is still managing the validator set.
	// Once the provider validator set starts validating blocks, the consumer CCV module
	// will take over proof of stake capabilities, but the standalone staking keeper will
	// stick around for slashing/jailing purposes.
	if state.PreCCV {
		k.SetPreCCVTrue(ctx)
		k.MarkAsPrevStandaloneChain(ctx)
		k.SetInitialValSet(ctx, state.Provider.InitialValSet)
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
		var clientID string
		if state.ConnectionId == "" {
			// create the provider client in InitGenesis for new consumer chain. CCV Handshake must be established with this client id.
			cid, err := k.clientKeeper.CreateClient(ctx, state.Provider.ClientState, state.Provider.ConsensusState)
			if err != nil {
				// If the client creation fails, the chain MUST NOT start
				panic(err)
			}
			clientID = cid

			k.Logger(ctx).Info("create new provider chain client",
				"client id", clientID,
			)
		} else {
			// if connection id is provided, then the client is already created
			connectionEnd, found := k.connectionKeeper.GetConnection(ctx, state.ConnectionId)
			if !found {
				panic(errorsmod.Wrapf(conntypes.ErrConnectionNotFound, "could not find connection(%s)", state.ConnectionId))
			}
			clientID = connectionEnd.ClientId

			k.Logger(ctx).Info("use existing client and connection to provider chain",
				"client id", clientID,
				"connection id", state.ConnectionId,
			)
		}

		// set provider client id.
		k.SetProviderClientID(ctx, clientID)

		// set default value for valset update ID
		k.SetHeightValsetUpdateID(ctx, uint64(ctx.BlockHeight()), uint64(0))

		if state.ConnectionId != "" {
			// initiate CCV channel handshake
			ccvChannelOpenInitMsg := channeltypes.NewMsgChannelOpenInit(
				ccv.ConsumerPortID,
				ccv.Version,
				channeltypes.ORDERED,
				[]string{state.ConnectionId},
				ccv.ProviderPortID,
				"", // signer unused
			)
			_, err := k.ChannelOpenInit(ctx, ccvChannelOpenInitMsg)
			if err != nil {
				panic(err)
			}

			// Note that if the connection ID is not provider, we cannot initiate
			// the connection handshake as the counterparty client ID is unknown
			// at this point. The connection handshake must be initiated by a relayer.
		}

	} else {
		// chain restarts with the CCV channel established
		if state.ProviderChannelId != "" {
			// set provider channel ID
			k.SetProviderChannel(ctx, state.ProviderChannelId)
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

		// Set pending consumer packets, using the depreciated ConsumerPacketDataList type
		// that exists for genesis.
		// note that the list includes pending mature VSC packet only if the handshake is completed
		for _, packet := range state.PendingConsumerPackets.List {
			k.AppendPendingPacket(ctx, packet.Type, packet.Data)
		}

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
	k.ApplyCCValidatorChanges(ctx, state.Provider.InitialValSet)
	return state.Provider.InitialValSet
}

// ExportGenesis returns the CCV consumer module's exported genesis
func (k Keeper) ExportGenesis(ctx sdk.Context) (genesis *types.GenesisState) {
	params := k.GetConsumerParams(ctx)
	if !params.Enabled {
		return types.DefaultGenesisState()
	}

	// export the current validator set
	valset := k.MustGetCurrentValidatorsAsABCIUpdates(ctx)

	// export pending packets using the depreciated ConsumerPacketDataList type
	pendingPackets := k.GetPendingPackets(ctx)
	pendingPacketsDepreciated := types.ConsumerPacketDataList{}
	pendingPacketsDepreciated.List = append(pendingPacketsDepreciated.List, pendingPackets...)

	// export all the states created after a provider channel got established
	if channelID, ok := k.GetProviderChannel(ctx); ok {
		clientID, found := k.GetProviderClientID(ctx)
		if !found {
			// This should never happen
			panic("provider client does not exist although provider channel does exist")
		}

		genesis = types.NewRestartGenesisState(
			clientID,
			channelID,
			valset,
			k.GetAllHeightToValsetUpdateIDs(ctx),
			pendingPacketsDepreciated,
			k.GetAllOutstandingDowntimes(ctx),
			k.GetLastTransmissionBlockHeight(ctx),
			params,
		)
	} else {
		clientID, ok := k.GetProviderClientID(ctx)
		// if provider clientID and channelID don't exist on the consumer chain,
		// then CCV protocol is disabled for this chain return a default genesis state
		if !ok {
			return types.DefaultGenesisState()
		}

		// export client states and pending slashing requests into a new chain genesis
		genesis = types.NewRestartGenesisState(
			clientID,
			"",
			valset,
			k.GetAllHeightToValsetUpdateIDs(ctx),
			pendingPacketsDepreciated,
			nil,
			types.LastTransmissionBlockHeight{},
			params,
		)
	}

	return genesis
}
