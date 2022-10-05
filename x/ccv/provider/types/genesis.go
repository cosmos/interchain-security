package types

import (
	"strings"

	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	types "github.com/cosmos/interchain-security/x/ccv/types"
)

func NewGenesisState(
	vscID uint64,
	vscIdToHeights []ValsetUpdateIdToHeight,
	consumerStates []ConsumerState,
	unbondingOps []types.UnbondingOp,
	matureUbdOps *ccv.MaturedUnbondingOps,
	additionProposals []ConsumerAdditionProposal,
	removalProposals []ConsumerRemovalProposal,
	params Params,
) *GenesisState {
	return &GenesisState{
		ValsetUpdateId:            vscID,
		ValsetUpdateIdToHeight:    vscIdToHeights,
		ConsumerStates:            consumerStates,
		UnbondingOps:              unbondingOps,
		MatureUnbondingOps:        matureUbdOps,
		ConsumerAdditionProposals: additionProposals,
		ConsumerRemovalProposals:  removalProposals,
		Params:                    params,
	}
}

func DefaultGenesisState() *GenesisState {
	return &GenesisState{
		Params: DefaultParams(),
	}
}

func (gs GenesisState) Validate() error {
	for _, cs := range gs.ConsumerStates {
		if err := cs.Validate(); err != nil {
			return err
		}
	}
	if err := gs.Params.Validate(); err != nil {
		return err
	}
	return nil
}

func (cs ConsumerState) Validate() error {
	if strings.TrimSpace(cs.ChainId) == "" {
		return sdkerrors.Wrap(sdkerrors.ErrInvalidChainID, "consumer chain id cannot be empty string")
	}
	if err := host.ChannelIdentifierValidator(cs.ChannelId); err != nil {
		return sdkerrors.Wrapf(err, "ccv channel id for chain %s is not valid", cs.ChainId)
	}
	return nil
}
