package types

import (
	"encoding/json"
	"fmt"
	"strings"

	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"

	tmtypes "github.com/cometbft/cometbft/proto/tendermint/types"

	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// provider message types
const (
	TypeMsgAssignConsumerKey          = "assign_consumer_key"
	TypeMsgSubmitConsumerMisbehaviour = "submit_consumer_misbehaviour"
	TypeMsgSubmitConsumerDoubleVoting = "submit_consumer_double_vote"
	TypeMsgOptIn                      = "opt_in"
	TypeMsgOptOut                     = "opt_out"
	TypeMsgSetConsumerCommissionRate  = "set_consumer_commission_rate"
)

var (
	_ sdk.Msg = (*MsgAssignConsumerKey)(nil)
	_ sdk.Msg = (*MsgConsumerAddition)(nil)
	_ sdk.Msg = (*MsgConsumerRemoval)(nil)
	_ sdk.Msg = (*MsgConsumerModification)(nil)
	_ sdk.Msg = (*MsgChangeRewardDenoms)(nil)
	_ sdk.Msg = (*MsgSubmitConsumerMisbehaviour)(nil)
	_ sdk.Msg = (*MsgSubmitConsumerDoubleVoting)(nil)
	_ sdk.Msg = (*MsgOptIn)(nil)
	_ sdk.Msg = (*MsgOptOut)(nil)
	_ sdk.Msg = (*MsgSetConsumerCommissionRate)(nil)

	_ sdk.HasValidateBasic = (*MsgAssignConsumerKey)(nil)
	_ sdk.HasValidateBasic = (*MsgConsumerAddition)(nil)
	_ sdk.HasValidateBasic = (*MsgConsumerRemoval)(nil)
	_ sdk.HasValidateBasic = (*MsgConsumerModification)(nil)
	_ sdk.HasValidateBasic = (*MsgChangeRewardDenoms)(nil)
	_ sdk.HasValidateBasic = (*MsgSubmitConsumerMisbehaviour)(nil)
	_ sdk.HasValidateBasic = (*MsgSubmitConsumerDoubleVoting)(nil)
	_ sdk.HasValidateBasic = (*MsgOptIn)(nil)
	_ sdk.HasValidateBasic = (*MsgOptOut)(nil)
	_ sdk.HasValidateBasic = (*MsgSetConsumerCommissionRate)(nil)
)

// NewMsgAssignConsumerKey creates a new MsgAssignConsumerKey instance.
// Delegator address and validator address are the same.
func NewMsgAssignConsumerKey(chainID string, providerValidatorAddress sdk.ValAddress,
	consumerConsensusPubKey, signer string,
) (*MsgAssignConsumerKey, error) {
	return &MsgAssignConsumerKey{
		ChainId:      chainID,
		ProviderAddr: providerValidatorAddress.String(),
		ConsumerKey:  consumerConsensusPubKey,
		Signer:       signer,
	}, nil
}

// Route implements the sdk.Msg interface.
func (msg MsgAssignConsumerKey) Route() string { return RouterKey }

// Type implements the sdk.Msg interface.
func (msg MsgAssignConsumerKey) Type() string {
	return TypeMsgAssignConsumerKey
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
// If the validator address is not same as delegator's, then the validator must
// sign the msg as well.
func (msg MsgAssignConsumerKey) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// GetSignBytes returns the message bytes to sign over.
func (msg MsgAssignConsumerKey) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgAssignConsumerKey) ValidateBasic() error {
	if strings.TrimSpace(msg.ChainId) == "" {
		return errorsmod.Wrapf(ErrInvalidConsumerChainID, "chainId cannot be blank")
	}
<<<<<<< HEAD
	// It is possible to assign keys for consumer chains that are not yet approved.
	// This can only be done by a signing validator, but it is still sensible
	// to limit the chainID size to prevent abuse.
	if 128 < len(msg.ChainId) {
		return errorsmod.Wrapf(ErrInvalidConsumerChainID, "chainId cannot exceed 128 length")
=======

	if err := ccvtypes.ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgAssignConsumerKey, "ConsumerId: %s", err.Error())
>>>>>>> 0d782959 (feat!: add memo to IBC transfers of ICS rewards (#2290))
	}
	valAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return ErrInvalidProviderAddress
	}
	// Check that the provider validator address and the signer address are the same
	if sdk.AccAddress(valAddr.Bytes()).String() != msg.Signer {
		return errorsmod.Wrapf(ErrInvalidProviderAddress, "provider validator address must be the same as the signer address")
	}
	if msg.ConsumerKey == "" {
		return ErrInvalidConsumerConsensusPubKey
	}
	if _, _, err := ParseConsumerKeyFromJson(msg.ConsumerKey); err != nil {
<<<<<<< HEAD
		return ErrInvalidConsumerConsensusPubKey
=======
		return errorsmod.Wrapf(ErrInvalidMsgAssignConsumerKey, "ConsumerKey: %s", err.Error())
	}

	return nil
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg *MsgChangeRewardDenoms) ValidateBasic() error {
	emptyDenomsToAdd := len(msg.DenomsToAdd) == 0
	emptyDenomsToRemove := len(msg.DenomsToRemove) == 0
	// Return error if both sets are empty or nil
	if emptyDenomsToAdd && emptyDenomsToRemove {
		return errorsmod.Wrapf(ErrInvalidMsgChangeRewardDenoms, "both DenomsToAdd and DenomsToRemove are empty")
	}

	denomMap := map[string]struct{}{}
	for _, denom := range msg.DenomsToAdd {
		// validate the denom
		if !sdk.NewCoin(denom, math.NewInt(1)).IsValid() {
			return errorsmod.Wrapf(ErrInvalidMsgChangeRewardDenoms, "DenomsToAdd: invalid denom(%s)", denom)
		}
		denomMap[denom] = struct{}{}
	}
	for _, denom := range msg.DenomsToRemove {
		// validate the denom
		if !sdk.NewCoin(denom, math.NewInt(1)).IsValid() {
			return errorsmod.Wrapf(ErrInvalidMsgChangeRewardDenoms, "DenomsToRemove: invalid denom(%s)", denom)
		}
		// denom cannot be in both sets
		if _, found := denomMap[denom]; found {
			return errorsmod.Wrapf(ErrInvalidMsgChangeRewardDenoms,
				"denom(%s) cannot be both added and removed", denom)
		}
	}

	return nil
}

func NewMsgSubmitConsumerMisbehaviour(
	consumerId string,
	submitter sdk.AccAddress,
	misbehaviour *ibctmtypes.Misbehaviour,
) (*MsgSubmitConsumerMisbehaviour, error) {
	return &MsgSubmitConsumerMisbehaviour{
		Submitter:    submitter.String(),
		Misbehaviour: misbehaviour,
		ConsumerId:   consumerId,
	}, nil
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgSubmitConsumerMisbehaviour) ValidateBasic() error {
	if err := ccvtypes.ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSubmitConsumerMisbehaviour, "ConsumerId: %s", err.Error())
	}

	if err := msg.Misbehaviour.ValidateBasic(); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSubmitConsumerMisbehaviour, "Misbehaviour: %s", err.Error())
>>>>>>> 0d782959 (feat!: add memo to IBC transfers of ICS rewards (#2290))
	}
	return nil
}

<<<<<<< HEAD
=======
func NewMsgSubmitConsumerDoubleVoting(
	consumerId string,
	submitter sdk.AccAddress,
	ev *tmtypes.DuplicateVoteEvidence,
	header *ibctmtypes.Header,
) (*MsgSubmitConsumerDoubleVoting, error) {
	return &MsgSubmitConsumerDoubleVoting{
		Submitter:             submitter.String(),
		DuplicateVoteEvidence: ev,
		InfractionBlockHeader: header,
		ConsumerId:            consumerId,
	}, nil
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgSubmitConsumerDoubleVoting) ValidateBasic() error {
	if dve, err := cmttypes.DuplicateVoteEvidenceFromProto(msg.DuplicateVoteEvidence); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSubmitConsumerDoubleVoting, "DuplicateVoteEvidence: %s", err.Error())
	} else {
		if err = dve.ValidateBasic(); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgSubmitConsumerDoubleVoting, "DuplicateVoteEvidence: %s", err.Error())
		}
	}

	if err := ValidateHeaderForConsumerDoubleVoting(msg.InfractionBlockHeader); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSubmitConsumerDoubleVoting, "ValidateTendermintHeader: %s", err.Error())
	}

	if err := ccvtypes.ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSubmitConsumerDoubleVoting, "ConsumerId: %s", err.Error())
	}

	return nil
}

// NewMsgOptIn creates a new NewMsgOptIn instance.
func NewMsgOptIn(consumerId string, providerValidatorAddress sdk.ValAddress, consumerConsensusPubKey, signer string) (*MsgOptIn, error) {
	return &MsgOptIn{
		ConsumerId:   consumerId,
		ProviderAddr: providerValidatorAddress.String(),
		ConsumerKey:  consumerConsensusPubKey,
		Signer:       signer,
	}, nil
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgOptIn) ValidateBasic() error {
	if err := validateDeprecatedChainId(msg.ChainId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptIn, "ChainId: %s", err.Error())
	}

	if err := ccvtypes.ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptIn, "ConsumerId: %s", err.Error())
	}

	if err := validateProviderAddress(msg.ProviderAddr, msg.Signer); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptIn, "ProviderAddr: %s", err.Error())
	}

	if msg.ConsumerKey != "" {
		if _, _, err := ParseConsumerKeyFromJson(msg.ConsumerKey); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgOptIn, "ConsumerKey: %s", err.Error())
		}
	}
	return nil
}

// NewMsgOptOut creates a new NewMsgOptIn instance.
func NewMsgOptOut(consumerId string, providerValidatorAddress sdk.ValAddress, signer string) (*MsgOptOut, error) {
	return &MsgOptOut{
		ConsumerId:   consumerId,
		ProviderAddr: providerValidatorAddress.String(),
		Signer:       signer,
	}, nil
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgOptOut) ValidateBasic() error {
	if err := validateDeprecatedChainId(msg.ChainId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptOut, "ChainId: %s", err.Error())
	}

	if err := ccvtypes.ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptOut, "ConsumerId: %s", err.Error())
	}

	if err := validateProviderAddress(msg.ProviderAddr, msg.Signer); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptOut, "ProviderAddr: %s", err.Error())
	}

	return nil
}

// NewMsgSetConsumerCommissionRate creates a new MsgSetConsumerCommissionRate msg instance.
func NewMsgSetConsumerCommissionRate(
	consumerId string,
	commission math.LegacyDec,
	providerValidatorAddress sdk.ValAddress,
	signer string,
) *MsgSetConsumerCommissionRate {
	return &MsgSetConsumerCommissionRate{
		ConsumerId:   consumerId,
		Rate:         commission,
		ProviderAddr: providerValidatorAddress.String(),
		Signer:       signer,
	}
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgSetConsumerCommissionRate) ValidateBasic() error {
	if err := validateDeprecatedChainId(msg.ChainId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSetConsumerCommissionRate, "ChainId: %s", err.Error())
	}

	if err := ccvtypes.ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSetConsumerCommissionRate, "ConsumerId: %s", err.Error())
	}

	if err := validateProviderAddress(msg.ProviderAddr, msg.Signer); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSetConsumerCommissionRate, "ProviderAddr: %s", err.Error())
	}

	if msg.Rate.IsNegative() || msg.Rate.GT(math.LegacyOneDec()) {
		return errorsmod.Wrapf(ErrInvalidMsgSetConsumerCommissionRate, "consumer commission rate should be in the range [0, 1]")
	}

	return nil
}

// NewMsgCreateConsumer creates a new MsgCreateConsumer instance
func NewMsgCreateConsumer(submitter, chainId string, metadata ConsumerMetadata,
	initializationParameters *ConsumerInitializationParameters, powerShapingParameters *PowerShapingParameters,
) (*MsgCreateConsumer, error) {
	return &MsgCreateConsumer{
		Submitter:                submitter,
		ChainId:                  chainId,
		Metadata:                 metadata,
		InitializationParameters: initializationParameters,
		PowerShapingParameters:   powerShapingParameters,
	}, nil
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgCreateConsumer) ValidateBasic() error {
	if err := ValidateStringField("ChainId", msg.ChainId, cmttypes.MaxChainIDLen); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "ChainId: %s", err.Error())
	}

	// With permissionless ICS, we can have multiple consumer chains with the exact same chain id.
	// However, as we already have the Neutron and Stride Top N chains running, as a first step we would like to
	// prevent permissionless chains from re-using the chain ids of Neutron and Stride. Note that this is just a
	// preliminary measure that will be removed later on as part of:
	// TODO (#2242): find a better way of ignoring past misbehaviors
	if msg.ChainId == "neutron-1" || msg.ChainId == "stride-1" {
		return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer,
			"cannot reuse chain ids of existing Neutron and Stride Top N consumer chains")
	}

	if err := ValidateConsumerMetadata(msg.Metadata); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "Metadata: %s", err.Error())
	}

	if msg.InitializationParameters != nil {
		if err := ValidateInitializationParameters(*msg.InitializationParameters); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "InitializationParameters: %s", err.Error())
		}
	}

	if msg.PowerShapingParameters != nil {
		if msg.PowerShapingParameters.Top_N != 0 {
			return fmt.Errorf("cannot create a Top N chain through `MsgCreateConsumer`; " +
				"first create the chain and then use `MsgUpdateConsumer` to make the chain Top N")
		}
		if err := ValidatePowerShapingParameters(*msg.PowerShapingParameters); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "PowerShapingParameters: %s", err.Error())
		}
	}

	return nil
}

// NewMsgUpdateConsumer creates a new MsgUpdateConsumer instance
func NewMsgUpdateConsumer(owner, consumerId, ownerAddress string, metadata *ConsumerMetadata,
	initializationParameters *ConsumerInitializationParameters, powerShapingParameters *PowerShapingParameters,
) (*MsgUpdateConsumer, error) {
	return &MsgUpdateConsumer{
		Owner:                    owner,
		ConsumerId:               consumerId,
		NewOwnerAddress:          ownerAddress,
		Metadata:                 metadata,
		InitializationParameters: initializationParameters,
		PowerShapingParameters:   powerShapingParameters,
	}, nil
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgUpdateConsumer) ValidateBasic() error {
	if err := ccvtypes.ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgUpdateConsumer, "ConsumerId: %s", err.Error())
	}

	// Note that NewOwnerAddress is validated when handling the message in UpdateConsumer

	if msg.Metadata != nil {
		if err := ValidateConsumerMetadata(*msg.Metadata); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgUpdateConsumer, "Metadata: %s", err.Error())
		}
	}

	if msg.InitializationParameters != nil {
		if err := ValidateInitializationParameters(*msg.InitializationParameters); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgUpdateConsumer, "InitializationParameters: %s", err.Error())
		}
	}

	if msg.PowerShapingParameters != nil {
		if err := ValidatePowerShapingParameters(*msg.PowerShapingParameters); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgUpdateConsumer, "PowerShapingParameters: %s", err.Error())
		}
	}

	return nil
}

// NewMsgRemoveConsumer creates a new MsgRemoveConsumer instance
func NewMsgRemoveConsumer(owner, consumerId string) (*MsgRemoveConsumer, error) {
	return &MsgRemoveConsumer{
		Owner:      owner,
		ConsumerId: consumerId,
	}, nil
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgRemoveConsumer) ValidateBasic() error {
	if err := ccvtypes.ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
	}
	return nil
}

//
// Validation methods
//

>>>>>>> 0d782959 (feat!: add memo to IBC transfers of ICS rewards (#2290))
// ParseConsumerKeyFromJson parses the consumer key from a JSON string,
// this replaces deserializing a protobuf any.
func ParseConsumerKeyFromJson(jsonStr string) (pkType, key string, err error) {
	type PubKey struct {
		Type string `json:"@type"`
		Key  string `json:"key"`
	}
	var pubKey PubKey
	err = json.Unmarshal([]byte(jsonStr), &pubKey)
	if err != nil {
		return "", "", err
	}
	return pubKey.Type, pubKey.Key, nil
}

func NewMsgSubmitConsumerMisbehaviour(submitter sdk.AccAddress, misbehaviour *ibctmtypes.Misbehaviour) (*MsgSubmitConsumerMisbehaviour, error) {
	return &MsgSubmitConsumerMisbehaviour{Submitter: submitter.String(), Misbehaviour: misbehaviour}, nil
}

// Route implements the sdk.Msg interface.
func (msg MsgSubmitConsumerMisbehaviour) Route() string { return RouterKey }

// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerMisbehaviour) Type() string {
	return TypeMsgSubmitConsumerMisbehaviour
}

// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerMisbehaviour) ValidateBasic() error {
	if msg.Submitter == "" {
		return errorsmod.Wrap(sdkerrors.ErrInvalidAddress, msg.Submitter)
	}

	if err := msg.Misbehaviour.ValidateBasic(); err != nil {
		return err
	}
	return nil
}

// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerMisbehaviour) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerMisbehaviour) GetSigners() []sdk.AccAddress {
	addr, err := sdk.AccAddressFromBech32(msg.Submitter)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{addr}
}

func NewMsgSubmitConsumerDoubleVoting(submitter sdk.AccAddress, ev *tmtypes.DuplicateVoteEvidence, header *ibctmtypes.Header) (*MsgSubmitConsumerDoubleVoting, error) {
	return &MsgSubmitConsumerDoubleVoting{Submitter: submitter.String(), DuplicateVoteEvidence: ev, InfractionBlockHeader: header}, nil
}

// Route implements the sdk.Msg interface.
func (msg MsgSubmitConsumerDoubleVoting) Route() string { return RouterKey }

// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerDoubleVoting) Type() string {
	return TypeMsgSubmitConsumerDoubleVoting
}

// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerDoubleVoting) ValidateBasic() error {
	if msg.Submitter == "" {
		return errorsmod.Wrap(sdkerrors.ErrInvalidAddress, msg.Submitter)
	}
	if msg.DuplicateVoteEvidence == nil {
		return fmt.Errorf("double voting evidence cannot be nil")
	}

	if msg.InfractionBlockHeader == nil {
		return fmt.Errorf("infraction block header cannot be nil")
	}

	if msg.InfractionBlockHeader.SignedHeader == nil {
		return fmt.Errorf("signed header in infraction block header cannot be nil")
	}

	if msg.InfractionBlockHeader.SignedHeader.Header == nil {
		return fmt.Errorf("invalid signed header in infraction block header, 'SignedHeader.Header' is nil")
	}

	if msg.InfractionBlockHeader.ValidatorSet == nil {
		return fmt.Errorf("invalid infraction block header, validator set is nil")
	}

	return nil
}

<<<<<<< HEAD
// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerDoubleVoting) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerDoubleVoting) GetSigners() []sdk.AccAddress {
	addr, err := sdk.AccAddressFromBech32(msg.Submitter)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{addr}
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
// If the validator address is not same as delegator's, then the validator must
// sign the msg as well.
func (msg *MsgConsumerAddition) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.Authority)
=======
// ValidateStringField validates that a string `field` satisfies the following properties:
//   - is not empty
//   - has at most `maxLength` characters
func ValidateStringField(nameOfTheField, field string, maxLength int) error {
	if strings.TrimSpace(field) == "" {
		return fmt.Errorf("%s cannot be empty", nameOfTheField)
	} else if len(field) > maxLength {
		return fmt.Errorf("%s is too long; got: %d, max: %d", nameOfTheField, len(field), maxLength)
	}
	return nil
}

// TruncateString truncates a string to maximum length characters
func TruncateString(str string, maxLength int) string {
	if maxLength <= 0 {
		return ""
	}

	truncated := ""
	count := 0
	for _, char := range str {
		truncated += string(char)
		count++
		if count >= maxLength {
			break
		}
	}
	return truncated
}

// ValidateConsumerMetadata validates that all the provided metadata are in the expected range
func ValidateConsumerMetadata(metadata ConsumerMetadata) error {
	if err := ValidateStringField("name", metadata.Name, MaxNameLength); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerMetadata, "Name: %s", err.Error())
	}

	if err := ValidateStringField("description", metadata.Description, MaxDescriptionLength); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerMetadata, "Description: %s", err.Error())
	}

	if err := ValidateStringField("metadata", metadata.Metadata, MaxMetadataLength); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerMetadata, "Metadata: %s", err.Error())
	}

	return nil
}

// ValidateConsAddressList validates a list of consensus addresses
func ValidateConsAddressList(list []string, maxLength int) error {
	if len(list) > maxLength {
		return fmt.Errorf("consensus address list too long;  got: %d, max: %d", len(list), maxLength)
	}
	for _, address := range list {
		_, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			return fmt.Errorf("invalid address %s: %s", address, err.Error())
		}
	}
	return nil
}

// ValidatePowerShapingParameters validates that all the provided power-shaping parameters are in the expected range
func ValidatePowerShapingParameters(powerShapingParameters PowerShapingParameters) error {
	// Top N corresponds to the top N% of validators that have to validate the consumer chain and can only be 0 (for an
	// Opt In chain) or in the range [50, 100] (for a Top N chain).
	if powerShapingParameters.Top_N != 0 && (powerShapingParameters.Top_N < 50 || powerShapingParameters.Top_N > 100) {
		return errorsmod.Wrap(ErrInvalidPowerShapingParameters, "Top N can either be 0 or in the range [50, 100]")
	}

	if powerShapingParameters.ValidatorsPowerCap > 100 {
		return errorsmod.Wrap(ErrInvalidPowerShapingParameters, "ValidatorsPowerCap has to be in the range [0, 100]")
	}

	if err := ValidateConsAddressList(powerShapingParameters.Allowlist, MaxValidatorCount); err != nil {
		return errorsmod.Wrapf(ErrInvalidPowerShapingParameters, "Allowlist: %s", err.Error())
	}
	if err := ValidateConsAddressList(powerShapingParameters.Denylist, MaxValidatorCount); err != nil {
		return errorsmod.Wrapf(ErrInvalidPowerShapingParameters, "Denylist: %s", err.Error())
	}

	return nil
}

// ValidateInitializationParameters validates that all the provided parameters are in the expected range
func ValidateInitializationParameters(initializationParameters ConsumerInitializationParameters) error {
	if initializationParameters.InitialHeight.IsZero() {
		return errorsmod.Wrap(ErrInvalidConsumerInitializationParameters, "InitialHeight cannot be zero")
	}

	if err := ValidateByteSlice(initializationParameters.GenesisHash, MaxHashLength); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "GenesisHash: %s", err.Error())
	}

	if err := ValidateByteSlice(initializationParameters.BinaryHash, MaxHashLength); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "BinaryHash: %s", err.Error())
	}

	if err := ccvtypes.ValidateStringFraction(initializationParameters.ConsumerRedistributionFraction); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "ConsumerRedistributionFraction: %s", err.Error())
	}

	if err := ccvtypes.ValidatePositiveInt64(initializationParameters.BlocksPerDistributionTransmission); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "BlocksPerDistributionTransmission: %s", err.Error())
	}

	if err := ccvtypes.ValidateDistributionTransmissionChannel(initializationParameters.DistributionTransmissionChannel); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "DistributionTransmissionChannel: %s", err.Error())
	}

	if err := ccvtypes.ValidatePositiveInt64(initializationParameters.HistoricalEntries); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "HistoricalEntries: %s", err.Error())
	}

	if err := ccvtypes.ValidateDuration(initializationParameters.CcvTimeoutPeriod); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "CcvTimeoutPeriod: %s", err.Error())
	}

	if err := ccvtypes.ValidateDuration(initializationParameters.TransferTimeoutPeriod); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "TransferTimeoutPeriod: %s", err.Error())
	}

	if err := ccvtypes.ValidateDuration(initializationParameters.UnbondingPeriod); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "UnbondingPeriod: %s", err.Error())
	}

	return nil
}

func ValidateByteSlice(hash []byte, maxLength int) error {
	if len(hash) > maxLength {
		return fmt.Errorf("hash is too long; got: %d, max: %d", len(hash), maxLength)
	}
	return nil
}

func validateDeprecatedChainId(chainId string) error {
	if strings.TrimSpace(chainId) != "" {
		return fmt.Errorf("found non-empty chainId(%s); chainId is deprecated, use consumerId instead", chainId)
	}

	return nil
}

// validateProviderAddress validates that the address is a sdk.ValAddress in Bech32 string format
func validateProviderAddress(addr, signer string) error {
	valAddr, err := sdk.ValAddressFromBech32(addr)
>>>>>>> 0d782959 (feat!: add memo to IBC transfers of ICS rewards (#2290))
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// ValidateBasic implements the sdk.Msg interface.
func (msg *MsgConsumerAddition) ValidateBasic() error {
	if strings.TrimSpace(msg.ChainId) == "" {
		return ErrBlankConsumerChainID
	}

	if msg.InitialHeight.IsZero() {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "initial height cannot be zero")
	}

	if len(msg.GenesisHash) == 0 {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "genesis hash cannot be empty")
	}
	if len(msg.BinaryHash) == 0 {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "binary hash cannot be empty")
	}

	if msg.SpawnTime.IsZero() {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "spawn time cannot be zero")
	}

	if err := ccvtypes.ValidateStringFraction(msg.ConsumerRedistributionFraction); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerAdditionProposal, "consumer redistribution fraction is invalid: %s", err)
	}

	if err := ccvtypes.ValidatePositiveInt64(msg.BlocksPerDistributionTransmission); err != nil {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "blocks per distribution transmission cannot be < 1")
	}

	if err := ccvtypes.ValidateDistributionTransmissionChannel(msg.DistributionTransmissionChannel); err != nil {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "distribution transmission channel")
	}

	if err := ccvtypes.ValidatePositiveInt64(msg.HistoricalEntries); err != nil {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "historical entries cannot be < 1")
	}

	if err := ccvtypes.ValidateDuration(msg.CcvTimeoutPeriod); err != nil {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "ccv timeout period cannot be zero")
	}

	if err := ccvtypes.ValidateDuration(msg.TransferTimeoutPeriod); err != nil {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "transfer timeout period cannot be zero")
	}

	if err := ccvtypes.ValidateDuration(msg.UnbondingPeriod); err != nil {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "unbonding period cannot be zero")
	}

	return nil
}

func (msg *MsgConsumerRemoval) ValidateBasic() error {

	if strings.TrimSpace(msg.ChainId) == "" {
		return errorsmod.Wrap(ErrInvalidConsumerRemovalProp, "consumer chain id must not be blank")
	}

	if msg.StopTime.IsZero() {
		return errorsmod.Wrap(ErrInvalidConsumerRemovalProp, "spawn time cannot be zero")
	}
	return nil
}

// ValidateBasic implements the sdk.Msg interface.
func (msg *MsgConsumerModification) ValidateBasic() error {
	if strings.TrimSpace(msg.ChainId) == "" {
		return ErrBlankConsumerChainID
	}

	err := ValidatePSSFeatures(msg.Top_N, msg.ValidatorsPowerCap)
	if err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerModificationProposal, "invalid PSS features: %s", err.Error())
	}

	return nil
}

// NewMsgOptIn creates a new NewMsgOptIn instance.
func NewMsgOptIn(chainID string, providerValidatorAddress sdk.ValAddress, consumerConsensusPubKey, signer string) (*MsgOptIn, error) {
	return &MsgOptIn{
		ChainId:      chainID,
		ProviderAddr: providerValidatorAddress.String(),
		ConsumerKey:  consumerConsensusPubKey,
		Signer:       signer,
	}, nil
}

// Type implements the sdk.Msg interface.
func (msg MsgOptIn) Type() string {
	return TypeMsgOptIn
}

// Route implements the sdk.Msg interface.
func (msg MsgOptIn) Route() string { return RouterKey }

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
func (msg MsgOptIn) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgOptIn) ValidateBasic() error {
	if strings.TrimSpace(msg.ChainId) == "" {
		return errorsmod.Wrapf(ErrInvalidConsumerChainID, "chainId cannot be blank")
	}
	// It is possible to opt in to validate on consumer chains that are not yet approved.
	// This can only be done by a signing validator, but it is still sensible
	// to limit the chainID size to prevent abuse.
	if 128 < len(msg.ChainId) {
		return errorsmod.Wrapf(ErrInvalidConsumerChainID, "chainId cannot exceed 128 length")
	}
	valAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return ErrInvalidProviderAddress
	}
	// Check that the provider validator address and the signer address are the same
	if sdk.AccAddress(valAddr.Bytes()).String() != msg.Signer {
		return errorsmod.Wrapf(ErrInvalidProviderAddress, "provider validator address must be the same as the signer address")
	}
	if msg.ConsumerKey != "" {
		if _, _, err := ParseConsumerKeyFromJson(msg.ConsumerKey); err != nil {
			return ErrInvalidConsumerConsensusPubKey
		}
	}
	return nil
}

// NewMsgOptOut creates a new NewMsgOptIn instance.
func NewMsgOptOut(chainID string, providerValidatorAddress sdk.ValAddress, signer string) (*MsgOptOut, error) {
	return &MsgOptOut{
		ChainId:      chainID,
		ProviderAddr: providerValidatorAddress.String(),
		Signer:       signer,
	}, nil
}

// Type implements the sdk.Msg interface.
func (msg MsgOptOut) Type() string {
	return TypeMsgOptOut
}

// Route implements the sdk.Msg interface.
func (msg MsgOptOut) Route() string { return RouterKey }

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
func (msg MsgOptOut) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// GetSignBytes returns the message bytes to sign over.
func (msg MsgOptOut) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgOptOut) ValidateBasic() error {
	if strings.TrimSpace(msg.ChainId) == "" {
		return errorsmod.Wrapf(ErrInvalidConsumerChainID, "chainId cannot be blank")
	}
	// It is possible to assign keys for consumer chains that are not yet approved.
	// This can only be done by a signing validator, but it is still sensible
	// to limit the chainID size to prevent abuse.
	if 128 < len(msg.ChainId) {
		return errorsmod.Wrapf(ErrInvalidConsumerChainID, "chainId cannot exceed 128 length")
	}
	valAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return ErrInvalidProviderAddress
	}
	// Check that the provider validator address and the signer address are the same
	if sdk.AccAddress(valAddr.Bytes()).String() != msg.Signer {
		return errorsmod.Wrapf(ErrInvalidProviderAddress, "provider validator address must be the same as the signer address")
	}

	return nil
}

// NewMsgSetConsumerCommissionRate creates a new MsgSetConsumerCommissionRate msg instance.
func NewMsgSetConsumerCommissionRate(chainID string, commission math.LegacyDec, providerValidatorAddress sdk.ValAddress, signer string) *MsgSetConsumerCommissionRate {
	return &MsgSetConsumerCommissionRate{
		ChainId:      chainID,
		Rate:         commission,
		ProviderAddr: providerValidatorAddress.String(),
		Signer:       signer,
	}
}

func (msg MsgSetConsumerCommissionRate) Route() string {
	return RouterKey
}

func (msg MsgSetConsumerCommissionRate) Type() string {
	return TypeMsgSetConsumerCommissionRate
}

func (msg MsgSetConsumerCommissionRate) ValidateBasic() error {
	if strings.TrimSpace(msg.ChainId) == "" {
		return errorsmod.Wrapf(ErrInvalidConsumerChainID, "chainId cannot be blank")
	}
	if 128 < len(msg.ChainId) {
		return errorsmod.Wrapf(ErrInvalidConsumerChainID, "chainId cannot exceed 128 length")
	}
	valAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return ErrInvalidProviderAddress
	}
	// Check that the provider validator address and the signer address are the same
	if sdk.AccAddress(valAddr.Bytes()).String() != msg.Signer {
		return errorsmod.Wrapf(ErrInvalidProviderAddress, "provider validator address must be the same as the signer address")
	}
	if msg.Rate.IsNegative() || msg.Rate.GT(math.LegacyOneDec()) {
		return errorsmod.Wrapf(ErrInvalidConsumerCommissionRate, "consumer commission rate should be in the range [0, 1]")
	}

	return nil
}

func (msg *MsgChangeRewardDenoms) ValidateBasic() error {
	emptyDenomsToAdd := len(msg.DenomsToAdd) == 0
	emptyDenomsToRemove := len(msg.DenomsToRemove) == 0
	// Return error if both sets are empty or nil
	if emptyDenomsToAdd && emptyDenomsToRemove {
		return fmt.Errorf(
			"invalid change reward denoms proposal: both denoms to add and denoms to remove are empty")
	}

	// Return error if a denom is in both sets
	for _, denomToAdd := range msg.DenomsToAdd {
		for _, denomToRemove := range msg.DenomsToRemove {
			if denomToAdd == denomToRemove {
				return fmt.Errorf(
					"invalid change reward denoms proposal: %s cannot be both added and removed", denomToAdd)
			}
		}
	}

	// Return error if any denom is "invalid"
	for _, denom := range msg.DenomsToAdd {
		if !sdk.NewCoin(denom, math.NewInt(1)).IsValid() {
			return fmt.Errorf("invalid change reward denoms proposal: %s is not a valid denom", denom)
		}
	}
	for _, denom := range msg.DenomsToRemove {
		if !sdk.NewCoin(denom, math.NewInt(1)).IsValid() {
			return fmt.Errorf("invalid change reward denoms proposal: %s is not a valid denom", denom)
		}
	}

	return nil
}

func (msg MsgSetConsumerCommissionRate) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

func (msg MsgSetConsumerCommissionRate) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}
