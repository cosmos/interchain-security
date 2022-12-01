package types

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
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
		ValsetUpdateId: DefaultValsetUpdateID,
		Params:         DefaultParams(),
	}
}

func (gs GenesisState) Validate() error {
	if gs.ValsetUpdateId == 0 {
		return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "valset update ID cannot be equal to zero")
	}

	for _, ubdOp := range gs.UnbondingOps {
		if len(ubdOp.UnbondingConsumerChains) == 0 {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "unbonding operations cannot have an empty consumer chain list")
		}
	}

	for _, prop := range gs.ConsumerAdditionProposals {
		if err := prop.ValidateBasic(); err != nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, err.Error())
		}
	}

	for _, prop := range gs.ConsumerRemovalProposals {
		if err := prop.ValidateBasic(); err != nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, err.Error())
		}
	}

	if len(gs.ValsetUpdateIdToHeight) > 1 {
		// check only the first tuple of the list since it is ordered by VSC ID
		if gs.ValsetUpdateIdToHeight[0].ValsetUpdateId == 0 {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, "valset update ID cannot be equal to zero")
		}
	}

	for _, cs := range gs.ConsumerStates {
		if err := cs.Validate(); err != nil {
			return sdkerrors.Wrap(ccv.ErrInvalidGenesis, fmt.Sprintf("%s: for consumer chain id: %s", err, cs.ChainId))
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
	if err := host.ChannelIdentifierValidator(cs.ChannelId); err != nil {
		return err
	}
	if err := host.ClientIdentifierValidator(cs.ClientId); err != nil {
		return err
	}
	// consumer genesis should be for a new chain only
	if !cs.ConsumerGenesis.NewChain {
		return fmt.Errorf("consumer genesis must be for a new chain")
	}
	// validate a new chain genesis
	if err := cs.ConsumerGenesis.Validate(); err != nil {
		return err
	}

	// validate optional fields

	if err := validateSlashAcksAddress(cs.SlashDowntimeAck); err != nil {
		return err
	}

	for _, pVSC := range cs.PendingValsetChanges {
		if pVSC.ValsetUpdateId == 0 {
			return fmt.Errorf("valset update ID cannot be equal to zero")
		}
		if len(pVSC.ValidatorUpdates) == 0 {
			return fmt.Errorf("validator set updates cannot be empty: %#v", pVSC)
		}
		if err := validateSlashAcksAddress(pVSC.SlashAcks); err != nil {
			return err
		}
	}

	for _, ubdOpIdx := range cs.UnbondingOpsIndex {
		if ubdOpIdx.ValsetUpdateId == 0 {
			return fmt.Errorf("valset update ID cannot be equal to zero")
		}
		if len(ubdOpIdx.UnbondingOpIndex) == 0 {
			return fmt.Errorf("unbonding operation index cannot be empty: %#v", ubdOpIdx)
		}
	}

	return nil
}

func validateSlashAcksAddress(acks []string) error {
	for _, a := range acks {
		if _, err := sdk.ConsAddressFromBech32(a); err != nil {
			return fmt.Errorf("invalid Bench32 address in slash downtime acks: %s", err)
		}
	}
	return nil
}
