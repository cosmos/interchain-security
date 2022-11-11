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
// The three states in which a consumer chain can start/restart:
//
//  1. A client to the provider was never created, i.e. a new consumer chain is started for the first time.
//  2. A consumer chain restarts after a client to the provider was created, but the CCV channel handshake is still in progress
//  3. A consumer chain restarts after the CCV channel handshake was completed.
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
	// start a new chain
	if state.NewChain {
		// create the provider client in InitGenesis for new consumer chain. CCV Handshake must be established with this client id.
		clientID, err := k.clientKeeper.CreateClient(ctx, state.ProviderClientState, state.ProviderConsensusState)
		if err != nil {
			panic(err)
		}

		// set provider client id.
		k.SetProviderClientID(ctx, clientID)

		// set default value for valset update ID
		k.SetHeightValsetUpdateID(ctx, uint64(ctx.BlockHeight()), uint64(0))
	} else {
		// verify genesis initial valset against the latest consensus state
		// IBC genesis MUST run before CCV consumer genesis
		if err := k.verifyGenesisInitValset(ctx, state); err != nil {
			panic(err)
		}
		// chain restarts without the CCV channel established
		if state.ProviderChannelId == "" {

			if len(state.PendingDataPackets.List) != 0 {
				k.SetPendingDataPackets(ctx, state.PendingDataPackets)
			}

			// chain restarts with the CCV channel established
		} else {
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

		// set height to valset update id mapping
		for _, h2v := range state.HeightToValsetUpdateId {
			k.SetHeightValsetUpdateID(ctx, h2v.Height, h2v.ValsetUpdateId)
		}

		// set provider client id
		k.SetProviderClientID(ctx, state.ProviderClientId)

	}

	// populate cross chain validators states with initial valset
	k.ApplyCCValidatorChanges(ctx, state.InitialValSet)

	return state.InitialValSet
}

// ExportGenesis returns the CCV consumer module's exported genesis
func (k Keeper) ExportGenesis(ctx sdk.Context) (genesis *consumertypes.GenesisState) {
	params := k.GetParams(ctx)
	if !params.Enabled {
		return consumertypes.DefaultGenesisState()
	}

	// export the current validator set
	valset, err := k.GetCurrentValidatorsAsABCIUpdates(ctx)
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
			k.GetHeightToValsetUpdateIDs(ctx),
			consumertypes.DataPackets{},
			outstandingDowntimes,
			consumertypes.LastTransmissionBlockHeight{},
			params,
		)
	} else {
		clientID, ok := k.GetProviderClientID(ctx)
		// if provider clientID and channelID don't exist on the consumer chain,
		// then CCV protocol is disabled for this chain return a default genesis state
		if !ok {
			return consumertypes.DefaultGenesisState()
		}

		pdp, _ := k.GetPendingDataPackets(ctx)

		// export client states and pending slashing requests into a new chain genesis
		genesis = consumertypes.NewRestartGenesisState(
			clientID,
			"",
			nil,
			valset,
			k.GetHeightToValsetUpdateIDs(ctx),
			pdp,
			nil,
			consumertypes.LastTransmissionBlockHeight{},
			params,
		)
	}

	return
}

// verifyGenesisInitValset verifies the latest consensus state on provider client matches
// the initial validator set of restarted chain thus
func (k Keeper) verifyGenesisInitValset(ctx sdk.Context, genState *consumertypes.GenesisState) error {

	consState, ok := k.clientKeeper.GetLatestClientConsensusState(ctx, genState.ProviderClientId)
	if !ok {
		return fmt.Errorf("consensus state for provider client not found. MUST run IBC genesis before CCV consumer genesis")
	}
	tmConsState, ok := consState.(*ibctmtypes.ConsensusState)
	if !ok {
		return fmt.Errorf(fmt.Sprintf("consensus state has wrong type. expected: %T, got: %T", &ibctmtypes.ConsensusState{}, consState))
	}

	// ensure that initial validator set is same as initial consensus state on provider client.
	// this will be verified by provider module on channel handshake.
	vals, err := tmtypes.PB2TM.ValidatorUpdates(genState.InitialValSet)
	if err != nil {
		return err
	}
	valSet := tmtypes.NewValidatorSet(vals)

	if !bytes.Equal(tmConsState.NextValidatorsHash, valSet.Hash()) {
		return fmt.Errorf("initial validator set does not match last consensus state of the provider client")
	}
	return nil
}
