package keeper

import (
	"bytes"
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// InitGenesis initializes the CCV consumer state and binds to PortID.
func (k Keeper) InitGenesis(ctx sdk.Context, state *consumertypes.GenesisState) []abci.ValidatorUpdate {
	k.SetParams(ctx, state.Params)
	// TODO: Remove enabled flag and find a better way to setup e2e tests
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
		k.SetProviderClientID(ctx, clientID)
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

		// set height to valset update id mapping
		for _, h2v := range state.HeightToValsetUpdateId {
			k.SetHeightValsetUpdateID(ctx, h2v.Height, h2v.ValsetUpdateId)
		}

		// set provider client id
		k.SetProviderClientID(ctx, state.ProviderClientId)
		// set provider channel id.
		k.SetProviderChannel(ctx, state.ProviderChannelId)
		// set all unbonding sequences
		for _, mp := range state.MaturingPackets {
			k.SetPacketMaturityTime(ctx, mp.VscId, mp.MaturityTime)
		}
	}

	// populate cross chain validators states with initial valset
	k.ApplyCCValidatorChanges(ctx, state.InitialValSet)

	return state.InitialValSet
}

// ExportGenesis exports the CCV consumer state. If the channel has already been established, then we export
// provider chain. Otherwise, this is still considered a new chain and we export latest client state.
func (k Keeper) ExportGenesis(ctx sdk.Context) (genesis *consumertypes.GenesisState) {
	params := k.GetParams(ctx)
	if !params.Enabled {
		return consumertypes.DefaultGenesisState()
	}

	// export the current validator set
	valset, err := k.GetValidatorUpdates(ctx)
	if err != nil {
		panic(fmt.Sprintf("fail to retrieve the validator set: %s", err))
	}

	// export all the states created after a provider channel got established
	if channelID, ok := k.GetProviderChannel(ctx); ok {
		clientID, ok := k.GetProviderClientID(ctx)
		if !ok {
			panic("provider client does not exist")
		}

		maturingPackets := []types.MaturingVSCPacket{}
		k.IteratePacketMaturityTime(ctx, func(vscId, timeNs uint64) bool {
			mat := types.MaturingVSCPacket{
				VscId:        vscId,
				MaturityTime: timeNs,
			}
			maturingPackets = append(maturingPackets, mat)
			return false
		})

		heightToVCIDs := []types.HeightToValsetUpdateID{}
		k.IterateHeightToValsetUpdateID(ctx, func(height, vscID uint64) bool {
			hv := types.HeightToValsetUpdateID{
				Height:         height,
				ValsetUpdateId: vscID,
			}
			heightToVCIDs = append(heightToVCIDs, hv)
			return true
		})

		outstandingDowntimes := []types.OutstandingDowntime{}
		k.IterateOutstandingDowntime(ctx, func(addr string) bool {
			od := types.OutstandingDowntime{
				ValidatorConsensusAddress: addr,
			}
			outstandingDowntimes = append(outstandingDowntimes, od)
			return true
		})

		genesis = types.NewRestartGenesisState(
			clientID,
			channelID,
			maturingPackets,
			valset,
			heightToVCIDs,
			outstandingDowntimes,
			params,
		)
	} else {
		clientID, ok := k.GetProviderClientID(ctx)
		// if provider clientID and channelID don't exist on the consumer chain, then CCV protocol is disabled for this chain
		// return a disabled genesis state
		if !ok {
			return consumertypes.DefaultGenesisState()
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
		// export client states and pending slashing requests into a new chain genesis
		genesis = consumertypes.NewInitialGenesisState(tmCs, tmConsState, valset, k.GetPendingSlashRequests(ctx), params)
	}

	return
}
