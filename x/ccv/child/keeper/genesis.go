package keeper

import (
	"bytes"
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/child/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// InitGenesis initializes the CCV child state and binds to PortID.
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
		// Create the parent client in InitGenesis for new child chain. CCV Handshake must be established with this client id.
		clientID, err := k.clientKeeper.CreateClient(ctx, state.ParentClientState, state.ParentConsensusState)
		if err != nil {
			panic(err)
		}

		// Set default value for valset update ID
		k.SetHeightValsetUpdateID(ctx, uint64(ctx.BlockHeight()), uint64(0))
		// set parent client id.
		k.SetParentClient(ctx, clientID)
	} else {
		// verify that latest consensus state on parent client matches the initial validator set of restarted chain
		// thus, IBC genesis MUST run before CCV child genesis
		consState, ok := k.clientKeeper.GetLatestClientConsensusState(ctx, state.ParentClientId)
		if !ok {
			panic("consensus state for parent client not found. MUST run IBC genesis before CCV child genesis")
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

		// set parent client id
		k.SetParentClient(ctx, state.ParentClientId)
		// set parent channel id.
		k.SetParentChannel(ctx, state.ParentChannelId)
		// set all unbonding sequences
		for _, us := range state.UnbondingSequences {
			k.SetUnbondingTime(ctx, us.Sequence, us.UnbondingTime)
			k.SetUnbondingPacket(ctx, us.Sequence, us.UnbondingPacket)
		}
	}

	k.ApplyCCValidatorChanges(ctx, state.InitialValSet)

	return state.InitialValSet
}

// ExportGenesis exports the CCV child state. If the channel has already been established, then we export
// parent chain. Otherwise, this is still considered a new chain and we export latest client state.
func (k Keeper) ExportGenesis(ctx sdk.Context) *types.GenesisState {
	params := k.GetParams(ctx)
	if !params.Enabled {
		return types.DefaultGenesisState()
	}

	if channelID, ok := k.GetParentChannel(ctx); ok {
		clientID, ok := k.GetParentClient(ctx)
		if !ok {
			panic("parent client does not exist")
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
	clientID, ok := k.GetParentClient(ctx)
	// if parent clientID and channelID don't exist on the child chain, then CCV protocol is disabled for this chain
	// return a disabled genesis state
	if !ok {
		return types.DefaultGenesisState()
	}
	cs, ok := k.clientKeeper.GetClientState(ctx, clientID)
	if !ok {
		panic("parent client not set on already running child chain")
	}
	tmCs, ok := cs.(*ibctmtypes.ClientState)
	if !ok {
		panic("parent client consensus state is not tendermint client state")
	}
	consState, ok := k.clientKeeper.GetLatestClientConsensusState(ctx, clientID)
	if !ok {
		panic("parent consensus state not set on already running child chain")
	}
	tmConsState, ok := consState.(*ibctmtypes.ConsensusState)
	if !ok {
		panic("parent consensus state is not tendermint consensus state")
	}
	// ValUpdates must be filled in off-line
	return types.NewInitialGenesisState(tmCs, tmConsState, nil, params)
}
