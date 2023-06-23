package types

import (
	"fmt"

	errorsmod "cosmossdk.io/errors"
	abci "github.com/cometbft/cometbft/abci/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
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

func (cp ConsumerPacketData) GetBytes() []byte {
	bytes := ModuleCdc.MustMarshalJSON(&cp)
	return bytes
}

type PacketAckResult []byte

var ( // slice types can't be const
	NoOpResult               = PacketAckResult([]byte{byte(1)})
	SlashPacketHandledResult = PacketAckResult([]byte{byte(2)})
	SlashPacketBouncedResult = PacketAckResult([]byte{byte(3)})
)

// An exported wrapper around the auto generated isConsumerPacketData_Data interface, only for
// AppendPendingPacket to accept the interface as an argument.
type ExportedIsConsumerPacketData_Data interface {
	isConsumerPacketData_Data
}

func NewConsumerPacketData(cpdType ConsumerPacketDataType, data isConsumerPacketData_Data, idx uint64) ConsumerPacketData {
	return ConsumerPacketData{
		Type: cpdType,
		Data: data,
		Idx:  idx,
	}
}
