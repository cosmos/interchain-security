package types

import (
	"bytes"

	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// NewInitialGenesisState returns a child GenesisState for a completely new child chain.
// TODO: Include chain status
func NewInitialGenesisState(cs *ibctmtypes.ClientState, consState *ibctmtypes.ConsensusState, initValSet []abci.ValidatorUpdate) *GenesisState {
	return &GenesisState{
		Params:               NewParams(true),
		NewChain:             true,
		ParentClientState:    cs,
		ParentConsensusState: consState,
		InitialValSet:        initValSet,
	}
}

// NewRestartGenesisState returns a child GenesisState that has already been established.
func NewRestartGenesisState(clientID, channelID string, unbondingSequences []UnbondingSequence, initValSet []abci.ValidatorUpdate) *GenesisState {
	return &GenesisState{
		Params:             NewParams(true),
		ParentClientId:     clientID,
		ParentChannelId:    channelID,
		UnbondingSequences: unbondingSequences,
		NewChain:           false,
		InitialValSet:      initValSet,
	}
}

// DefaultGenesisState returns a default disabled child chain genesis state. This allows the module to be hooked up to app without getting use
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

	if gs.NewChain {
		if gs.ParentClientState == nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "parent client state cannot be nil for new chain")
		}
		if err := gs.ParentClientState.Validate(); err != nil {
			return sdkerrors.Wrapf(ccv.ErrInvalidGenesis, "parent client state invalid for new chain %s", err.Error())
		}
		if gs.ParentConsensusState == nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "parent consensus state cannot be nil for new chain")
		}
		if err := gs.ParentConsensusState.ValidateBasic(); err != nil {
			return sdkerrors.Wrapf(ccv.ErrInvalidGenesis, "parent consensus state invalid for new chain %s", err.Error())
		}
		if gs.ParentClientId != "" {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "parent client id cannot be set for new chain. It must be established on handshake")
		}
		if gs.ParentChannelId != "" {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "parent channel id cannot be set for new chain. It must be established on handshake")
		}
		if gs.UnbondingSequences != nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "unbonding sequences must be nil for new chain")
		}

		// ensure that initial validator set is same as initial consensus state on provider client.
		// this will be verified by provider module on channel handshake.
		vals, err := tmtypes.PB2TM.ValidatorUpdates(gs.InitialValSet)
		if err != nil {
			return sdkerrors.Wrap(err, "could not convert val updates to validator set")
		}
		valSet := tmtypes.NewValidatorSet(vals)
		if !bytes.Equal(gs.ParentConsensusState.NextValidatorsHash, valSet.Hash()) {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "initial validators does not hash to NextValidatorsHash on provider client")
		}
	} else {
		// NOTE: For restart genesis, we will verify initial validator set in InitGenesis.
		if gs.ParentClientId == "" {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "parent client id must be set for a restarting child genesis state")
		}
		if gs.ParentChannelId == "" {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "parent channel id must be set for a restarting child genesis state")
		}
		if gs.ParentClientState != nil || gs.ParentConsensusState != nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "parent client state and consensus states must be nil for a restarting genesis state")
		}
		for _, us := range gs.UnbondingSequences {
			if err := us.Validate(); err != nil {
				return sdkerrors.Wrap(err, "invalid unbonding sequences")
			}
		}
	}
	return nil
}

func (us UnbondingSequence) Validate() error {
	if us.UnbondingTime == 0 {
		return sdkerrors.Wrap(ccv.ErrInvalidUnbondingTime, "cannot have 0 unbonding time")
	}
	if err := us.UnbondingPacket.ValidateBasic(); err != nil {
		return sdkerrors.Wrap(err, "invalid unbonding packet")
	}
	if us.UnbondingPacket.Sequence != us.Sequence {
		return sdkerrors.Wrapf(ccv.ErrInvalidUnbondingSequence, "unbonding sequence %d must match packet sequence %d", us.Sequence, us.UnbondingPacket.Sequence)
	}
	return nil
}
