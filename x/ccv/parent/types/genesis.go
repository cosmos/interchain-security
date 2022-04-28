package types

import (
	"fmt"

	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
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
	if cs.ChainId == "" {
		return fmt.Errorf("child chain id cannot be blank")
	}
	if err := host.ChannelIdentifierValidator(cs.ChannelId); err != nil {
		return sdkerrors.Wrapf(err, "ccv channel id for chain %s is not valid", cs.ChainId)
	}
	return nil
}
