package types

import (
	"encoding/json"
	"fmt"
	"strings"

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

	if cp.Type == SlashPacket {
		type Validator struct {
			Address string `json:"address"`
			Power   string `json:"power"`
		}
		type SlashPacketData struct {
			Validator      Validator `json:"validator"`
			ValsetUpdateID string    `json:"valset_update_id"`
			// Same as protbuf generated type, but infraction is string instead of enum
			Infraction string `json:"infraction"`
		}
		type NewSchema struct {
			Type            string          `json:"type"`
			SlashPacketData SlashPacketData `json:"slashPacketData"`
		}
		// Unmarshal the JSON string into the struct
		var data NewSchema
		err := json.Unmarshal(bytes, &data)
		if err != nil {
			panic(err)
		}

		// Modify the value of the "infraction" field By adding "TYPE" after first underscore
		data.SlashPacketData.Infraction = strings.Replace(
			data.SlashPacketData.Infraction, "_", "_TYPE_", 1)

		// Replace bytes with modified JSON string
		bytes, err = json.Marshal(data)
		if err != nil {
			return nil
		}
	}
	return bytes
}
