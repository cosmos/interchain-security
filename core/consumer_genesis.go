package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"

	abci "github.com/tendermint/tendermint/abci/types"
)

// NewInitialGenesisState returns a consumer GenesisState for a completely new consumer chain.
func NewInitialConsumerGenesisState(cs *ibctmtypes.ClientState, consState *ibctmtypes.ConsensusState,
	initValSet []abci.ValidatorUpdate, params ConsumerParams,
) *ConsumerGenesisState {
	return &ConsumerGenesisState{
		Params:                 params,
		NewChain:               true,
		ProviderClientState:    cs,
		ProviderConsensusState: consState,
		InitialValSet:          initValSet,
	}
}

// NewRestartGenesisState returns a consumer GenesisState that has already been established.
func NewRestartConsumerGenesisState(
	clientID, channelID string,
	maturingPackets []MaturingVSCPacket,
	initValSet []abci.ValidatorUpdate,
	heightToValsetUpdateIDs []HeightToValsetUpdateID,
	pendingConsumerPackets ConsumerPacketDataList,
	outstandingDowntimes []OutstandingDowntime,
	lastTransBlockHeight LastTransmissionBlockHeight,
	params ConsumerParams,
) *ConsumerGenesisState {
	return &ConsumerGenesisState{
		Params:                      params,
		ProviderClientId:            clientID,
		ProviderChannelId:           channelID,
		MaturingPackets:             maturingPackets,
		NewChain:                    false,
		InitialValSet:               initValSet,
		HeightToValsetUpdateId:      heightToValsetUpdateIDs,
		PendingConsumerPackets:      pendingConsumerPackets,
		OutstandingDowntimeSlashing: outstandingDowntimes,
		LastTransmissionBlockHeight: lastTransBlockHeight,
	}
}

// DefaultGenesisState returns a default disabled consumer chain genesis state. This allows the module to be hooked up to app without getting use
// unless explicitly specified in genesis.
func DefaultConsumerGenesisState() *ConsumerGenesisState {
	return &ConsumerGenesisState{
		Params: DefaultConsumerParams(),
	}
}

// Validate performs basic genesis state validation returning an error upon any failure.
//
// The three cases where a consumer chain starts/restarts
// expect the following optional and mandatory genesis states:
//
// 1. New chain starts:
//   - Params, InitialValset, provider client state, provider consensus state // mandatory
//
// 2. Chain restarts with CCV handshake still in progress:
//   - Params, InitialValset, ProviderID, HeightToValidatorSetUpdateID // mandatory
//   - PendingConsumerPacket // optional
//
// 3. Chain restarts with CCV handshake completed:
//   - Params, InitialValset, ProviderID, channelID, HeightToValidatorSetUpdateID // mandatory
//   - MaturingVSCPackets, OutstandingDowntime, PendingConsumerPacket, LastTransmissionBlockHeight // optional
//

func (gs ConsumerGenesisState) Validate() error {
	if !gs.Params.Enabled {
		return nil
	}
	if len(gs.InitialValSet) == 0 {
		return sdkerrors.Wrap(ErrInvalidGenesis, "initial validator set is empty")
	}
	if err := gs.Params.Validate(); err != nil {
		return err
	}

	if gs.NewChain {
		if gs.ProviderClientState == nil {
			return sdkerrors.Wrap(ErrInvalidGenesis, "provider client state cannot be nil for new chain")
		}
		if err := gs.ProviderClientState.Validate(); err != nil {
			return sdkerrors.Wrapf(ErrInvalidGenesis, "provider client state invalid for new chain %s", err.Error())
		}
		if gs.ProviderConsensusState == nil {
			return sdkerrors.Wrap(ErrInvalidGenesis, "provider consensus state cannot be nil for new chain")
		}
		if err := gs.ProviderConsensusState.ValidateBasic(); err != nil {
			return sdkerrors.Wrapf(ErrInvalidGenesis, "provider consensus state invalid for new chain %s", err.Error())
		}
		if gs.ProviderClientId != "" {
			return sdkerrors.Wrap(ErrInvalidGenesis, "provider client id cannot be set for new chain. It must be established on handshake")
		}
		if gs.ProviderChannelId != "" {
			return sdkerrors.Wrap(ErrInvalidGenesis, "provider channel id cannot be set for new chain. It must be established on handshake")
		}
		if len(gs.MaturingPackets) != 0 {
			return sdkerrors.Wrap(ErrInvalidGenesis, "maturing packets must be empty for new chain")
		}
		if len(gs.PendingConsumerPackets.List) != 0 {
			return sdkerrors.Wrap(ErrInvalidGenesis, "pending consumer packets must be empty for new chain")
		}
		if gs.LastTransmissionBlockHeight.Height != 0 {
			return sdkerrors.Wrap(ErrInvalidGenesis, "last transmission block height must be empty for new chain")
		}
	} else {
		// NOTE: For restart genesis, we will verify initial validator set in InitGenesis.
		if gs.ProviderClientId == "" {
			return sdkerrors.Wrap(ErrInvalidGenesis, "provider client id must be set for a restarting consumer genesis state")
		}
		// handshake is still in progress
		handshakeInProgress := gs.ProviderChannelId == ""
		if handshakeInProgress {
			if len(gs.MaturingPackets) != 0 {
				return sdkerrors.Wrap(
					ErrInvalidGenesis, "maturing packets must be empty when handshake isn't completed")
			}
			if len(gs.OutstandingDowntimeSlashing) != 0 {
				return sdkerrors.Wrap(
					ErrInvalidGenesis, "outstanding downtime must be empty when handshake isn't completed")
			}
			if gs.LastTransmissionBlockHeight.Height != 0 {
				return sdkerrors.Wrap(
					ErrInvalidGenesis, "last transmission block height must be zero when handshake isn't completed")
			}
			if len(gs.PendingConsumerPackets.List) != 0 {
				for _, packet := range gs.PendingConsumerPackets.List {
					if packet.Type == VscMaturedPacket {
						return sdkerrors.Wrap(ErrInvalidGenesis, "pending maturing packets must be empty when handshake isn't completed")
					}
				}
			}
		}
		if gs.HeightToValsetUpdateId == nil {
			return sdkerrors.Wrap(
				ErrInvalidGenesis,
				"empty height to validator set update id mapping",
			)
		}
		if gs.ProviderClientState != nil || gs.ProviderConsensusState != nil {
			return sdkerrors.Wrap(ErrInvalidGenesis, "provider client state and consensus state must be nil for a restarting genesis state")
		}
		for _, mat := range gs.MaturingPackets {
			if err := mat.Validate(); err != nil {
				return sdkerrors.Wrap(err, "invalid unbonding sequences")
			}
		}
	}
	return nil
}

func (mat MaturingVSCPacket) Validate() error {
	if mat.MaturityTime.IsZero() {
		return sdkerrors.Wrap(ErrInvalidVSCMaturedTime, "cannot have 0 maturity time")
	}
	if mat.VscId == 0 {
		return sdkerrors.Wrap(ErrInvalidVSCMaturedId, "cannot have 0 maturity time")
	}
	return nil
}
