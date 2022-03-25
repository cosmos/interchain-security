package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	abci "github.com/tendermint/tendermint/abci/types"
)

func NewValidatorSetChangePacketData(valUpdates []abci.ValidatorUpdate, valUpdateID uint64, penaltyAcks []string) ValidatorSetChangePacketData {
	return ValidatorSetChangePacketData{
		ValidatorUpdates: valUpdates,
		ValsetUpdateId:   valUpdateID,
		PenaltyAcks:      penaltyAcks,
	}
}

// ValidateBasic is used for validating the CCV packet data.
func (vsc ValidatorSetChangePacketData) ValidateBasic() error {
	if len(vsc.ValidatorUpdates) == 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "validator updates cannot be empty")
	}
	return nil
}

func (vsc ValidatorSetChangePacketData) GetBytes() []byte {
	valUpdateBytes := ModuleCdc.MustMarshalJSON(&vsc)
	return valUpdateBytes
}

func NewValidatorPenaltyPacketData(validator abci.Validator, valUpdateId uint64, slashFraction, jailTime int64) ValidatorPenaltyPacketData {
	return ValidatorPenaltyPacketData{
		Validator:      validator,
		SlashFraction:  slashFraction,
		JailTime:       jailTime,
		ValsetUpdateId: valUpdateId,
	}
}

func (vdt ValidatorPenaltyPacketData) ValidateBasic() error {
	if len(vdt.Validator.Address) == 0 || vdt.Validator.Power == 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "validator fields cannot be empty")
	}
	// allow slahing with 0 jail time
	if vdt.JailTime < 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "jail duration must be positive")
	}

	if vdt.SlashFraction <= 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "slash fraction must be positive")
	}

	if vdt.ValsetUpdateId == 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "valset update id cannot be equal to zero")
	}

	return nil
}

func (vdt ValidatorPenaltyPacketData) GetBytes() []byte {
	valDowntimeBytes := ModuleCdc.MustMarshalJSON(&vdt)
	return valDowntimeBytes
}
