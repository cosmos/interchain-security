package types

import (
	"fmt"
	"strings"

	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

func NewGenesisState(
	vscID uint64,
	vscIdToHeights []ValsetUpdateIdToHeight,
	consumerStates []ConsumerState,
	unbondingOps []ccv.UnbondingOp,
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

// Validate performs a consumer state validation returning an error upon any failure.
// It ensures that the chain id, client id and consumer genesis states are valid and non-empty.
func (cs ConsumerState) Validate() error {
	if strings.TrimSpace(cs.ChainId) == "" {
		return sdkerrors.Wrap(sdkerrors.ErrInvalidChainID, "consumer chain id cannot be empty string")
	}
	if err := host.ChannelIdentifierValidator(cs.ChannelId); err != nil {
		return sdkerrors.Wrapf(err, "ccv channel id for chain %s is not valid", cs.ChainId)
	}
	if cs.ClientId == "" {
		return sdkerrors.Wrap(ccv.ErrInvalidGenesis, fmt.Sprintf("client id must be set for consumer chain %s", cs.ChainId))
	}
	// consumer genesis should be for a new chain only
	if !cs.ConsumerGenesis.NewChain {
		return sdkerrors.Wrap(ccv.ErrInvalidGenesis, cs.ChainId)
	}
	// validate a new chain genesis
	if err := cs.ConsumerGenesis.Validate(); err != nil {
		return sdkerrors.Wrap(ccv.ErrInvalidGenesis, err.Error())
	}

	return nil
}
