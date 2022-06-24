package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func NewValidatorSetChangePacketData(valUpdates []abci.ValidatorUpdate, valUpdateID uint64, SlashAcks []string) ValidatorSetChangePacketData {
	return ValidatorSetChangePacketData{
		ValidatorUpdates: valUpdates,
		ValsetUpdateId:   valUpdateID,
		SlashAcks:        SlashAcks,
	}
}

// ValidateBasic is used for validating the CCV packet data.
func (vsc ValidatorSetChangePacketData) ValidateBasic() error {
	if len(vsc.ValidatorUpdates) == 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "validator updates cannot be empty")
	}
	if vsc.ValsetUpdateId == 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "valset update id cannot be equal to zero")
	}
	return nil
}

func (vsc ValidatorSetChangePacketData) GetBytes() []byte {
	valUpdateBytes := ModuleCdc.MustMarshalJSON(&vsc)
	return valUpdateBytes
}

func NewVSCMaturedPacketData(valUpdateID uint64) VSCMaturedPacketData {
	return VSCMaturedPacketData{
		ValsetUpdateId: valUpdateID,
	}
}

// ValidateBasic is used for validating the VSCMatured packet data.
func (mat VSCMaturedPacketData) ValidateBasic() error {
	if mat.ValsetUpdateId == 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "vscId cannot be equal to zero")
	}
	return nil
}

func (mat VSCMaturedPacketData) GetBytes() []byte {
	bytes := ModuleCdc.MustMarshalJSON(&mat)
	return bytes
}

func NewSlashPacketData(validator abci.Validator, valUpdateId uint64, infractionType stakingtypes.InfractionType) SlashPacketData {
	return SlashPacketData{
		Validator:      validator,
		ValsetUpdateId: valUpdateId,
		Infraction:     infractionType,
	}
}

func (vdt SlashPacketData) ValidateBasic() error {
	if len(vdt.Validator.Address) == 0 || vdt.Validator.Power == 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "validator fields cannot be empty")
	}
	if vdt.ValsetUpdateId == 0 {
		return sdkerrors.Wrap(ErrInvalidPacketData, "valset update id cannot be equal to zero")
	}

	if vdt.Infraction == stakingtypes.InfractionEmpty {
		return sdkerrors.Wrap(ErrInvalidPacketData, "invalid infraction type")
	}

	return nil
}

func (vdt SlashPacketData) GetBytes() []byte {
	valDowntimeBytes := ModuleCdc.MustMarshalJSON(&vdt)
	return valDowntimeBytes
}
