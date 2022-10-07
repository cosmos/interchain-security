package types

import (
	"bytes"

	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// NewInitialGenesisState returns a consumer GenesisState for a completely new consumer chain.
func NewInitialGenesisState(cs *ibctmtypes.ClientState, consState *ibctmtypes.ConsensusState,
	initValSet []abci.ValidatorUpdate, slashRequests SlashRequests, params Params) *GenesisState {

	return &GenesisState{
		Params:                 params,
		NewChain:               true,
		ProviderClientState:    cs,
		ProviderConsensusState: consState,
		InitialValSet:          initValSet,
		PendingSlashRequests:   slashRequests,
	}
}

// NewRestartGenesisState returns a consumer GenesisState that has already been established.
func NewRestartGenesisState(clientID, channelID string,
	maturingPackets []MaturingVSCPacket,
	initValSet []abci.ValidatorUpdate,
	heightToValsetUpdateIDs []HeightToValsetUpdateID,
	outstandingDowntimes []OutstandingDowntime,
	params Params,
) *GenesisState {

	return &GenesisState{
		Params:                      params,
		ProviderClientId:            clientID,
		ProviderChannelId:           channelID,
		MaturingPackets:             maturingPackets,
		NewChain:                    false,
		InitialValSet:               initValSet,
		HeightToValsetUpdateId:      heightToValsetUpdateIDs,
		OutstandingDowntimeSlashing: outstandingDowntimes,
	}
}

// DefaultGenesisState returns a default disabled consumer chain genesis state. This allows the module to be hooked up to app without getting use
// unless explicitly specified in genesis.
func DefaultGenesisState() *GenesisState {
	return &GenesisState{
		Params: DefaultParams(),
	}
}

// Validate performs basic genesis state validation returning an error upon any failure.
func (gs GenesisState) Validate() error {
	if !gs.Params.Enabled {
		return nil
	}
	if len(gs.InitialValSet) == 0 {
		return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "initial validator set is empty")
	}
	if err := gs.Params.Validate(); err != nil {
		return err
	}

	if gs.NewChain {
		if gs.ProviderClientState == nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "provider client state cannot be nil for new chain")
		}
		if err := gs.ProviderClientState.Validate(); err != nil {
			return sdkerrors.Wrapf(ccv.ErrInvalidGenesis, "provider client state invalid for new chain %s", err.Error())
		}
		if gs.ProviderConsensusState == nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "provider consensus state cannot be nil for new chain")
		}
		if err := gs.ProviderConsensusState.ValidateBasic(); err != nil {
			return sdkerrors.Wrapf(ccv.ErrInvalidGenesis, "provider consensus state invalid for new chain %s", err.Error())
		}
		if gs.ProviderClientId != "" {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "provider client id cannot be set for new chain. It must be established on handshake")
		}
		if gs.ProviderChannelId != "" {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "provider channel id cannot be set for new chain. It must be established on handshake")
		}
		if len(gs.MaturingPackets) != 0 {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "maturing packets must be empty for new chain")
		}

		// ensure that initial validator set is same as initial consensus state on provider client.
		// this will be verified by provider module on channel handshake.
		vals, err := tmtypes.PB2TM.ValidatorUpdates(gs.InitialValSet)
		if err != nil {
			return sdkerrors.Wrap(err, "could not convert val updates to validator set")
		}
		valSet := tmtypes.NewValidatorSet(vals)
		if !bytes.Equal(gs.ProviderConsensusState.NextValidatorsHash, valSet.Hash()) {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "initial validators does not hash to NextValidatorsHash on provider client")
		}
	} else {
		// NOTE: For restart genesis, we will verify initial validator set in InitGenesis.
		if gs.ProviderClientId == "" {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "provider client id must be set for a restarting consumer genesis state")
		}
		if gs.ProviderChannelId == "" {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "provider channel id must be set for a restarting consumer genesis state")
		}
		if gs.ProviderClientState != nil || gs.ProviderConsensusState != nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "provider client state and consensus states must be nil for a restarting genesis state")
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
	if mat.MaturityTime == 0 {
		return sdkerrors.Wrap(ccv.ErrInvalidVSCMaturedTime, "cannot have 0 maturity time")
	}
	if mat.VscId == 0 {
		return sdkerrors.Wrap(ccv.ErrInvalidVSCMaturedId, "cannot have 0 maturity time")
	}
	return nil
}
