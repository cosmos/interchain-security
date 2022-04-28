package keeper

import (
	"bytes"
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// InitGenesis initializes the CCV consumer state and binds to PortID.
func (k Keeper) InitGenesis(ctx sdk.Context, state *types.GenesisState) []abci.ValidatorUpdate {
	k.SetParams(ctx, state.Params)
	if !state.Params.Enabled {
		return nil
	}

	k.SetPort(ctx, types.PortID)

	// Only try to bind to port if it is not already bound, since we may already own
	// port capability from capability InitGenesis
	if !k.IsBound(ctx, types.PortID) {
		// transfer module binds to the transfer port on InitChain
		// and claims the returned capability
		err := k.BindPort(ctx, types.PortID)
		if err != nil {
			panic(fmt.Sprintf("could not claim port capability: %v", err))
		}
	}

	// initialValSet is checked in NewChain case by ValidateGenesis
	if state.NewChain {
		// Create the provider client in InitGenesis for new consumer chain. CCV Handshake must be established with this client id.
		clientID, err := k.clientKeeper.CreateClient(ctx, state.ProviderClientState, state.ProviderConsensusState)
		if err != nil {
			panic(err)
		}

		// Set default value for valset update ID
		k.SetHeightValsetUpdateID(ctx, uint64(ctx.BlockHeight()), uint64(0))
		// set provider client id.
		k.SetProviderClient(ctx, clientID)
	} else {
		// verify that latest consensus state on provider client matches the initial validator set of restarted chain
		// thus, IBC genesis MUST run before CCV consumer genesis
		consState, ok := k.clientKeeper.GetLatestClientConsensusState(ctx, state.ProviderClientId)
		if !ok {
			panic("consensus state for provider client not found. MUST run IBC genesis before CCV consumer genesis")
		}
		tmConsState, ok := consState.(*ibctmtypes.ConsensusState)
		if !ok {
			panic(fmt.Sprintf("consensus state has wrong type. expected: %T, got: %T", &ibctmtypes.ConsensusState{}, consState))
		}

		// ensure that initial validator set is same as initial consensus state on provider client.
		// this will be verified by provider module on channel handshake.
		vals, err := tmtypes.PB2TM.ValidatorUpdates(state.InitialValSet)
		if err != nil {
			panic(err)
		}
		valSet := tmtypes.NewValidatorSet(vals)

		if !bytes.Equal(tmConsState.NextValidatorsHash, valSet.Hash()) {
			panic("initial validator set does not match last consensus state of the provider client")
		}

		// set provider client id
		k.SetProviderClient(ctx, state.ProviderClientId)
		// set provider channel id.
		k.SetProviderChannel(ctx, state.ProviderChannelId)
		// set all unbonding sequences
		for _, us := range state.UnbondingSequences {
			k.SetUnbondingTime(ctx, us.Sequence, us.UnbondingTime)
			k.SetUnbondingPacket(ctx, us.Sequence, us.UnbondingPacket)
		}
	}

	k.ApplyCCValidatorChanges(ctx, state.InitialValSet)

	return state.InitialValSet
}

// ExportGenesis exports the CCV consumer state. If the channel has already been established, then we export
// provider chain. Otherwise, this is still considered a new chain and we export latest client state.
func (k Keeper) ExportGenesis(ctx sdk.Context) *types.GenesisState {
	params := k.GetParams(ctx)
	if !params.Enabled {
		return types.DefaultGenesisState()
	}

	if channelID, ok := k.GetProviderChannel(ctx); ok {
		clientID, ok := k.GetProviderClient(ctx)
		if !ok {
			panic("provider client does not exist")
		}
		// ValUpdates must be filled in off-line
		gs := types.NewRestartGenesisState(clientID, channelID, nil, nil, params)

		unbondingSequences := []types.UnbondingSequence{}
		cb := func(seq uint64, packet channeltypes.Packet) bool {
			timeNs := k.GetUnbondingTime(ctx, seq)
			us := types.UnbondingSequence{
				Sequence:        seq,
				UnbondingTime:   timeNs,
				UnbondingPacket: packet,
			}
			unbondingSequences = append(unbondingSequences, us)
			return false
		}
		k.IterateUnbondingPacket(ctx, cb)

		gs.UnbondingSequences = unbondingSequences
		return gs
	}
	clientID, ok := k.GetProviderClient(ctx)
	// if provider clientID and channelID don't exist on the consumer chain, then CCV protocol is disabled for this chain
	// return a disabled genesis state
	if !ok {
		return types.DefaultGenesisState()
	}
	cs, ok := k.clientKeeper.GetClientState(ctx, clientID)
	if !ok {
		panic("provider client not set on already running consumer chain")
	}
	tmCs, ok := cs.(*ibctmtypes.ClientState)
	if !ok {
		panic("provider client consensus state is not tendermint client state")
	}
	consState, ok := k.clientKeeper.GetLatestClientConsensusState(ctx, clientID)
	if !ok {
		panic("provider consensus state not set on already running consumer chain")
	}
	tmConsState, ok := consState.(*ibctmtypes.ConsensusState)
	if !ok {
		panic("provider consensus state is not tendermint consensus state")
	}
	// ValUpdates must be filled in off-line
	return types.NewInitialGenesisState(tmCs, tmConsState, nil, params)
}
