package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	host "github.com/cosmos/ibc-go/modules/core/24-host"
)

func NewGenesisState(childStates []ChildState, params Params) *GenesisState {
	return &GenesisState{
		ChildStates: childStates,
		Params:      params,
	}
}

func DefaultGenesisState() *GenesisState {
	return &GenesisState{
		Params: DefaultParams(),
	}
}

func (gs GenesisState) Validate() error {
	for _, cs := range gs.ChildStates {
		if err := cs.Validate(); err != nil {
			return err
		}
	}
	if err := gs.Params.Validate(); err != nil {
		return err
	}
	return nil
}

func (cs ChildState) Validate() error {
	if err := host.ClientIdentifierValidator(cs.ChainId); err != nil {
		return sdkerrors.Wrap(err, "child chain id cannot be blank")
	}
	if err := host.ChannelIdentifierValidator(cs.ChannelId); err != nil {
		return sdkerrors.Wrapf(err, "ccv channel id for %s cannot be blank", cs.ChainId)
	}
	return nil
}
