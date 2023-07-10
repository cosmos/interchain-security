package types

import (
	"fmt"

	errorsmod "cosmossdk.io/errors"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"
)

func NewValidatorSetChangePacketData(valUpdates []abci.ValidatorUpdate, valUpdateID uint64, slashAcks []string) ValidatorSetChangePacketData {
	return ValidatorSetChangePacketData{
		ValidatorUpdates: valUpdates,
		ValsetUpdateId:   valUpdateID,
		SlashAcks:        slashAcks,
	}
}

// ValidateBasic is used for validating the CCV packet data.
func (vsc ValidatorSetChangePacketData) ValidateBasic() error {
	if len(vsc.ValidatorUpdates) == 0 {
		return errorsmod.Wrap(ErrInvalidPacketData, "validator updates cannot be empty")
	}
	if vsc.ValsetUpdateId == 0 {
		return errorsmod.Wrap(ErrInvalidPacketData, "valset update id cannot be equal to zero")
	}
	return nil
}

func (vsc ValidatorSetChangePacketData) GetBytes() []byte {
	valUpdateBytes := ModuleCdc.MustMarshalJSON(&vsc)
	return valUpdateBytes
}

func NewVSCMaturedPacketData(valUpdateID uint64) *VSCMaturedPacketData {
	return &VSCMaturedPacketData{
		ValsetUpdateId: valUpdateID,
	}
}

// ValidateBasic is used for validating the VSCMatured packet data.
func (mat VSCMaturedPacketData) ValidateBasic() error {
	if mat.ValsetUpdateId == 0 {
		return errorsmod.Wrap(ErrInvalidPacketData, "vscId cannot be equal to zero")
	}
	return nil
}

func (mat VSCMaturedPacketData) GetBytes() []byte {
	bytes := ModuleCdc.MustMarshalJSON(&mat)
	return bytes
}

func NewSlashPacketData(validator abci.Validator, valUpdateId uint64, infractionType stakingtypes.Infraction) *SlashPacketData {
	return &SlashPacketData{
		Validator:      validator,
		ValsetUpdateId: valUpdateId,
		Infraction:     infractionType,
	}
}

// NewSlashPacketDataV1 creates a new SlashPacketDataV1 that uses ccv.InfractionTypes to maintain backward compatibility.
func NewSlashPacketDataV1(validator abci.Validator, valUpdateId uint64, infractionType stakingtypes.Infraction) *SlashPacketDataV1 {
	v1Type := InfractionEmpty
	switch infractionType {
	case stakingtypes.Infraction_INFRACTION_DOWNTIME:
		v1Type = Downtime
	case stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN:
		v1Type = DoubleSign
	}

	return &SlashPacketDataV1{
		Validator:      validator,
		ValsetUpdateId: valUpdateId,
		Infraction:     v1Type,
	}
}

func (vdt SlashPacketData) ValidateBasic() error {
	if len(vdt.Validator.Address) == 0 || vdt.Validator.Power == 0 {
		return errorsmod.Wrap(ErrInvalidPacketData, "validator fields cannot be empty")
	}

	if vdt.Infraction == stakingtypes.Infraction_INFRACTION_UNSPECIFIED {
		return errorsmod.Wrap(ErrInvalidPacketData, "invalid infraction type")
	}

	return nil
}

func (vdt SlashPacketData) GetBytes() []byte {
	valDowntimeBytes := ModuleCdc.MustMarshalJSON(&vdt)
	return valDowntimeBytes
}

func (vdt SlashPacketData) ToV1() *SlashPacketDataV1 {
	return NewSlashPacketDataV1(vdt.Validator, vdt.ValsetUpdateId, vdt.Infraction)
}

func (cp ConsumerPacketData) ValidateBasic() (err error) {
	switch cp.Type {
	case VscMaturedPacket:
		// validate VSCMaturedPacket
		vscPacket := cp.GetVscMaturedPacketData()
		if vscPacket == nil {
			return fmt.Errorf("invalid consumer packet data: VscMaturePacketData data cannot be empty")
		}
		err = vscPacket.ValidateBasic()
	case SlashPacket:
		// validate SlashPacket
		slashPacket := cp.GetSlashPacketData()
		if slashPacket == nil {
			return fmt.Errorf("invalid consumer packet data: SlashPacketData data cannot be empty")
		}
		err = slashPacket.ValidateBasic()
	default:
		err = fmt.Errorf("invalid consumer packet type: %q", cp.Type)
	}

	return
}

// Convert to bytes while maintaining over the wire compatibility with previous versions.
func (cp ConsumerPacketData) GetBytes() []byte {
	return cp.ToV1Bytes()
}

// ToV1Bytes converts the ConsumerPacketData to JSON byte array compatible
// with the format used by ICS versions using cosmos-sdk v45 (ICS v1 and ICS v2).
func (cp ConsumerPacketData) ToV1Bytes() []byte {
	if cp.Type != SlashPacket {
		bytes := ModuleCdc.MustMarshalJSON(&cp)
		return bytes
	}

	sp := cp.GetSlashPacketData()
	spdv1 := NewSlashPacketDataV1(sp.Validator, sp.ValsetUpdateId, sp.Infraction)
	cpv1 := ConsumerPacketDataV1{
		Type: cp.Type,
		Data: &ConsumerPacketDataV1_SlashPacketData{
			SlashPacketData: spdv1,
		},
	}
	bytes := ModuleCdc.MustMarshalJSON(&cpv1)
	return bytes
}

// FromV1 converts SlashPacketDataV1 to SlashPacketData.
// Provider must handle both V1 and later versions of the SlashPacketData.
func (vdt1 SlashPacketDataV1) FromV1() *SlashPacketData {
	newType := stakingtypes.Infraction_INFRACTION_UNSPECIFIED
	switch vdt1.Infraction {
	case Downtime:
		newType = stakingtypes.Infraction_INFRACTION_DOWNTIME
	case DoubleSign:
		newType = stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN
	}

	return &SlashPacketData{
		Validator:      vdt1.Validator,
		ValsetUpdateId: vdt1.ValsetUpdateId,
		Infraction:     newType,
	}
}
