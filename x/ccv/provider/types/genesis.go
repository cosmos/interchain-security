package types

import (
	"fmt"

	host "github.com/cosmos/ibc-go/v7/modules/core/24-host"

	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

func NewGenesisState(
	vscID uint64,
	vscIdToHeights []ValsetUpdateIdToHeight,
	consumerStates []ConsumerState,
	unbondingOps []UnbondingOp,
	matureUbdOps *ccv.MaturedUnbondingOps,
	additionProposals []ConsumerAdditionProposal,
	removalProposals []ConsumerRemovalProposal,
	params Params,
	validatorConsumerPubkeys []ValidatorConsumerPubKey,
	validatorsByConsumerAddr []ValidatorByConsumerAddr,
	consumerAddrsToPrune []ConsumerAddrsToPrune,
	initTimeoutTimestamps []InitTimeoutTimestamp,
	exportedVscSendTimestamps []ExportedVscSendTimestamp,
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
		ValidatorConsumerPubkeys:  validatorConsumerPubkeys,
		ValidatorsByConsumerAddr:  validatorsByConsumerAddr,
		ConsumerAddrsToPrune:      consumerAddrsToPrune,
		InitTimeoutTimestamps:     initTimeoutTimestamps,
		ExportedVscSendTimestamps: exportedVscSendTimestamps,
	}
}

func DefaultGenesisState() *GenesisState {
	return &GenesisState{
		// ensure that VSCID is strictly positive
		ValsetUpdateId: DefaultValsetUpdateID,
		Params:         DefaultParams(),
	}
}

func (gs GenesisState) Validate() error {
	if gs.ValsetUpdateId == 0 {
		return errorsmod.Wrap(ccv.ErrInvalidGenesis, "valset update ID cannot be equal to zero")
	}

	for _, ubdOp := range gs.UnbondingOps {
		if err := gs.ValidateUnbondingOp(ubdOp); err != nil {
			return err
		}
	}

	for _, prop := range gs.ConsumerAdditionProposals {
		if err := prop.ValidateBasic(); err != nil {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, err.Error())
		}
	}

	for _, prop := range gs.ConsumerRemovalProposals {
		if err := prop.ValidateBasic(); err != nil {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, err.Error())
		}
	}

	if len(gs.ValsetUpdateIdToHeight) > 0 {
		// check only the first tuple of the list since it is ordered by VSC ID
		if gs.ValsetUpdateIdToHeight[0].ValsetUpdateId == 0 {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, "valset update ID cannot be equal to zero")
		}
	}

	for _, cs := range gs.ConsumerStates {
		if err := cs.Validate(); err != nil {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis, fmt.Sprintf("%s: for consumer chain id: %s", err, cs.ChainId))
		}
	}

	if err := gs.Params.Validate(); err != nil {
		return err
	}

	if err := KeyAssignmentValidateBasic(gs.ValidatorConsumerPubkeys,
		gs.ValidatorsByConsumerAddr,
		gs.ConsumerAddrsToPrune,
	); err != nil {
		return err
	}

	return nil
}

func (gs GenesisState) ValidateUnbondingOp(ubdOp UnbondingOp) error {
	if len(ubdOp.UnbondingConsumerChains) == 0 {
		return errorsmod.Wrap(ccv.ErrInvalidGenesis, "unbonding operations cannot have an empty consumer chain list")
	}

	// Check that the ID is set correctly in the UnbondingOpsIndex
	for _, chainID := range ubdOp.UnbondingConsumerChains {
		found := false

		// Find consumer state for this consumer chain
		for _, cs := range gs.ConsumerStates {
			if cs.ChainId != chainID {
				continue
			}
			for _, vscUnbondingOps := range cs.UnbondingOpsIndex {
				for _, id := range vscUnbondingOps.GetUnbondingOpIds() {
					if id == ubdOp.Id {
						found = true
						break
					}
				}
			}
		}
		if !found {
			return errorsmod.Wrap(ccv.ErrInvalidGenesis,
				fmt.Sprintf("unbonding operation without UnbondingOpsIndex, opID=%d, chainID=%s", ubdOp.Id, chainID))
		}
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
		if err := validateSlashAcksAddress(pVSC.SlashAcks); err != nil {
			return err
		}
	}

	for _, ubdOpIdx := range cs.UnbondingOpsIndex {
		if ubdOpIdx.VscId == 0 {
			return fmt.Errorf("UnbondingOpsIndex vscID cannot be equal to zero")
		}
		if len(ubdOpIdx.UnbondingOpIds) == 0 {
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
