package types

import (
	ibctmtypes "github.com/cosmos/ibc-go/v9/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"

	abci "github.com/cometbft/cometbft/abci/types"

	ccv "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

// NewRestartGenesisState returns a consumer GenesisState that has already been established.
func NewRestartGenesisState(
	clientID, channelID string,
	initValSet []abci.ValidatorUpdate,
	heightToValsetUpdateIDs []HeightToValsetUpdateID,
	pendingConsumerPackets ConsumerPacketDataList,
	outstandingDowntimes []OutstandingDowntime,
	lastTransBlockHeight LastTransmissionBlockHeight,
	params ccv.ConsumerParams,
) *GenesisState {
	return &GenesisState{
		NewChain: false,
		Params:   params,
		Provider: ccv.ProviderInfo{
			InitialValSet: initValSet,
		},
		HeightToValsetUpdateId:      heightToValsetUpdateIDs,
		PendingConsumerPackets:      pendingConsumerPackets,
		OutstandingDowntimeSlashing: outstandingDowntimes,
		LastTransmissionBlockHeight: lastTransBlockHeight,
		ProviderClientId:            clientID,
		ProviderChannelId:           channelID,
	}
}

// DefaultGenesisState returns a default disabled consumer chain genesis state. This allows the module to be hooked up to app without getting use
// unless explicitly specified in genesis.
func DefaultGenesisState() *GenesisState {
	return &GenesisState{
		Params: ccv.DefaultParams(),
	}
}

// NewInitialGenesisState returns a GenesisState for a completely new consumer chain.
func NewInitialGenesisState(cs *ibctmtypes.ClientState, consState *ibctmtypes.ConsensusState,
	initValSet []abci.ValidatorUpdate, params ccv.ConsumerParams,
) *GenesisState {
	return &GenesisState{
		NewChain: true,
		Params:   params,
		Provider: ccv.ProviderInfo{
			ClientState:    cs,
			ConsensusState: consState,
			InitialValSet:  initValSet,
		},
	}
}

// Validate performs basic genesis state validation returning an error upon any failure.
//
// The three cases where a consumer chain starts/restarts
// expect the following optional and mandatory genesis states:
//
// 1. New chain starts:
//   - Params, InitialValset // mandatory
//
// 1a. ConnectionId is empty
//   - provider client state, provider consensus state // mandatory
//
// 1b. ConnectionId is not empty
//   - provider client state, provider consensus state // nil
//
// 2. Chain restarts with CCV handshake still in progress:
//   - Params, InitialValset, ProviderID, HeightToValidatorSetUpdateID // mandatory
//   - PendingConsumerPacket // optional
//
// 3. Chain restarts with CCV handshake completed:
//   - Params, InitialValset, ProviderID, channelID, HeightToValidatorSetUpdateID // mandatory
//   - MaturingVSCPackets, OutstandingDowntime, PendingConsumerPacket, LastTransmissionBlockHeight // optional
func (gs GenesisState) Validate() error {
	if !gs.Params.Enabled {
		return nil
	}
	if len(gs.Provider.InitialValSet) == 0 {
		return errorsmod.Wrap(ccv.ErrInvalidGenesis, "initial validator set is empty")
	}
	if err := gs.Params.Validate(); err != nil {
		return err
	}

	if gs.NewChain {
		if gs.ConnectionId == "" {
			// connection ID is not provided
			if gs.Provider.ClientState == nil {
				return errorsmod.Wrap(ccv.ErrInvalidGenesis, "provider client state cannot be nil for new chain")
			}
			if err := gs.Provider.ClientState.Validate(); err != nil {
				return errorsmod.Wrapf(ccv.ErrInvalidGenesis, "provider client state invalid for new chain %s", err.Error())
			}
			if gs.Provider.ConsensusState == nil {
				return errorsmod.Wrap(ccv.ErrInvalidGenesis, "provider consensus state cannot be nil for new chain")
			}
			if err := gs.Provider.ConsensusState.ValidateBasic(); err != nil {
				return errorsmod.Wrapf(ccv.ErrInvalidGenesis, "provider consensus state invalid for new chain %s", err.Error())
			}
		} else {
			// connection ID is provided
			if gs.Provider.ClientState != nil {
				return errorsmod.Wrap(ccv.ErrInvalidGenesis, "provider client state must be nil when connection id is provided")
			}
			if gs.Provider.ConsensusState != nil {
				return errorsmod.Wrap(ccv.ErrInvalidGenesis, "provider consensus state must be nil when connection id is provided")
			}
			if err := ccv.ValidateConnectionIdentifier(gs.ConnectionId); err != nil {
				return errorsmod.Wrapf(ccv.ErrInvalidGenesis, "invalid connection id: %s", err.Error())
			}
		}

		if gs.ProviderClientId != "" {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, "provider client id cannot be set for new chain. It must be established on handshake")
		}
		if gs.ProviderChannelId != "" {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, "provider channel id cannot be set for new chain. It must be established on handshake")
		}
		if len(gs.HeightToValsetUpdateId) != 0 {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, "HeightToValsetUpdateId must be nil for new chain")
		}
		if len(gs.OutstandingDowntimeSlashing) != 0 {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, "OutstandingDowntimeSlashing must be nil for new chain")
		}
		if len(gs.PendingConsumerPackets.List) != 0 {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, "pending consumer packets must be empty for new chain")
		}
		if gs.LastTransmissionBlockHeight.Height != 0 {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, "last transmission block height must be empty for new chain")
		}
	} else {
		// NOTE: For restart genesis, we will verify initial validator set in InitGenesis.
		if gs.ProviderClientId == "" {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, "provider client id must be set for a restarting consumer genesis state")
		}
		// handshake is still in progress
		handshakeInProgress := gs.ProviderChannelId == ""
		if handshakeInProgress {
			if len(gs.OutstandingDowntimeSlashing) != 0 {
				return errorsmod.Wrap(
					ccv.ErrInvalidGenesis, "outstanding downtime must be empty when handshake in progress")
			}
			if gs.LastTransmissionBlockHeight.Height != 0 {
				return errorsmod.Wrap(
					ccv.ErrInvalidGenesis, "last transmission block height must be zero when handshake in progress")
			}
			if len(gs.PendingConsumerPackets.List) != 0 {
				for _, packet := range gs.PendingConsumerPackets.List {
					if packet.Type == ccv.VscMaturedPacket {
						return errorsmod.Wrap(ccv.ErrInvalidGenesis, "pending maturing packets must be empty when handshake isn't completed")
					}
				}
			}
		}
		/* 		if gs.HeightToValsetUpdateId == nil {
			return errorsmod.Wrap(
				ccv.ErrInvalidGenesis,
				"empty height to validator set update id mapping",
			)
		} */
		if gs.Provider.ClientState != nil || gs.Provider.ConsensusState != nil {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, "provider client state and consensus state must be nil for a restarting genesis state")
		}
	}
	return nil
}
