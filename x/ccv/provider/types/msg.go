package types

import (
	"encoding/json"
	"fmt"
	"strconv"
	"strings"
	"time"

	cmttypes "github.com/cometbft/cometbft/types"

	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"

	tmtypes "github.com/cometbft/cometbft/proto/tendermint/types"

	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// provider message types
const (
	TypeMsgAssignConsumerKey          = "assign_consumer_key"
	TypeMsgSubmitConsumerMisbehaviour = "submit_consumer_misbehaviour"
	TypeMsgSubmitConsumerDoubleVoting = "submit_consumer_double_vote"
	TypeMsgCreateConsumer             = "create_consumer"
	TypeMsgUpdateConsumer             = "update_consumer"
	TypeMsgRemoveConsumer             = "remove_consumer"
	TypeMsgOptIn                      = "opt_in"
	TypeMsgOptOut                     = "opt_out"
	TypeMsgSetConsumerCommissionRate  = "set_consumer_commission_rate"

	// MaxNameLength defines the maximum consumer name length
	MaxNameLength = 50
	// MaxDescriptionLength defines the maximum consumer description length
	MaxDescriptionLength = 10000
	// MaxMetadataLength defines the maximum consumer metadata length
	MaxMetadataLength = 255
	// MaxHashLength defines the maximum length of a hash
	MaxHashLength = 64
	// MaxValidatorCount defines the maximum number of validators
	MaxValidatorCount = 1000
)

var (
	_ sdk.Msg = (*MsgAssignConsumerKey)(nil)
	_ sdk.Msg = (*MsgChangeRewardDenoms)(nil)
	_ sdk.Msg = (*MsgSubmitConsumerMisbehaviour)(nil)
	_ sdk.Msg = (*MsgSubmitConsumerDoubleVoting)(nil)
	_ sdk.Msg = (*MsgCreateConsumer)(nil)
	_ sdk.Msg = (*MsgUpdateConsumer)(nil)
	_ sdk.Msg = (*MsgRemoveConsumer)(nil)
	_ sdk.Msg = (*MsgOptIn)(nil)
	_ sdk.Msg = (*MsgOptOut)(nil)
	_ sdk.Msg = (*MsgSetConsumerCommissionRate)(nil)

	_ sdk.HasValidateBasic = (*MsgAssignConsumerKey)(nil)
	_ sdk.HasValidateBasic = (*MsgChangeRewardDenoms)(nil)
	_ sdk.HasValidateBasic = (*MsgSubmitConsumerMisbehaviour)(nil)
	_ sdk.HasValidateBasic = (*MsgSubmitConsumerDoubleVoting)(nil)
	_ sdk.HasValidateBasic = (*MsgCreateConsumer)(nil)
	_ sdk.HasValidateBasic = (*MsgUpdateConsumer)(nil)
	_ sdk.HasValidateBasic = (*MsgRemoveConsumer)(nil)
	_ sdk.HasValidateBasic = (*MsgOptIn)(nil)
	_ sdk.HasValidateBasic = (*MsgOptOut)(nil)
	_ sdk.HasValidateBasic = (*MsgSetConsumerCommissionRate)(nil)
)

// NewMsgAssignConsumerKey creates a new MsgAssignConsumerKey instance.
// Delegator address and validator address are the same.
func NewMsgAssignConsumerKey(consumerId string, providerValidatorAddress sdk.ValAddress,
	consumerConsensusPubKey, signer string,
) (*MsgAssignConsumerKey, error) {
	return &MsgAssignConsumerKey{
		ConsumerId:   consumerId,
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

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgAssignConsumerKey) ValidateBasic() error {
	if err := validateDeprecatedChainId(msg.ChainId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgAssignConsumerKey, "ChainId: %s", err.Error())
	}

	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgAssignConsumerKey, "ConsumerId: %s", err.Error())
	}

	_, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgAssignConsumerKey, "ProviderAddr: %s", err.Error())
	}

	if msg.ConsumerKey == "" {
		return errorsmod.Wrapf(ErrInvalidMsgAssignConsumerKey, "ConsumerKey cannot be empty")
	}
	if _, _, err := ParseConsumerKeyFromJson(msg.ConsumerKey); err != nil {
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

func NewMsgSubmitConsumerMisbehaviour(
	submitter sdk.AccAddress,
	misbehaviour *ibctmtypes.Misbehaviour,
) (*MsgSubmitConsumerMisbehaviour, error) {
	return &MsgSubmitConsumerMisbehaviour{
		Submitter:    submitter.String(),
		Misbehaviour: misbehaviour,
	}, nil
}

// Route implements the sdk.Msg interface.
func (msg MsgSubmitConsumerMisbehaviour) Route() string { return RouterKey }

// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerMisbehaviour) Type() string {
	return TypeMsgSubmitConsumerMisbehaviour
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgSubmitConsumerMisbehaviour) ValidateBasic() error {
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSubmitConsumerMisbehaviour, "ConsumerId: %s", err.Error())
	}

	if err := msg.Misbehaviour.ValidateBasic(); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSubmitConsumerMisbehaviour, "Misbehaviour: %s", err.Error())
	}
	return nil
}

func NewMsgSubmitConsumerDoubleVoting(
	submitter sdk.AccAddress,
	ev *tmtypes.DuplicateVoteEvidence,
	header *ibctmtypes.Header,
) (*MsgSubmitConsumerDoubleVoting, error) {
	return &MsgSubmitConsumerDoubleVoting{
		Submitter:             submitter.String(),
		DuplicateVoteEvidence: ev,
		InfractionBlockHeader: header,
	}, nil
}

// Route implements the sdk.Msg interface.
func (msg MsgSubmitConsumerDoubleVoting) Route() string { return RouterKey }

// Type implements the sdk.Msg interface.
func (msg MsgSubmitConsumerDoubleVoting) Type() string {
	return TypeMsgSubmitConsumerDoubleVoting
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

	if err := ValidateTendermintHeader(msg.InfractionBlockHeader); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSubmitConsumerDoubleVoting, "ValidateTendermintHeader: %s", err.Error())
	}

	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
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

// Type implements the sdk.Msg interface.
func (msg MsgOptIn) Type() string {
	return TypeMsgOptIn
}

// Route implements the sdk.Msg interface.
func (msg MsgOptIn) Route() string { return RouterKey }

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgOptIn) ValidateBasic() error {
	if err := validateDeprecatedChainId(msg.ChainId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptIn, "ChainId: %s", err.Error())
	}

	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptIn, "ConsumerId: %s", err.Error())
	}

	_, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
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

// Type implements the sdk.Msg interface.
func (msg MsgOptOut) Type() string {
	return TypeMsgOptOut
}

// Route implements the sdk.Msg interface.
func (msg MsgOptOut) Route() string { return RouterKey }

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgOptOut) ValidateBasic() error {
	if err := validateDeprecatedChainId(msg.ChainId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptOut, "ChainId: %s", err.Error())
	}

	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgOptOut, "ConsumerId: %s", err.Error())
	}

	_, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
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

func (msg MsgSetConsumerCommissionRate) Route() string {
	return RouterKey
}

func (msg MsgSetConsumerCommissionRate) Type() string {
	return TypeMsgSetConsumerCommissionRate
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgSetConsumerCommissionRate) ValidateBasic() error {
	if err := validateDeprecatedChainId(msg.ChainId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSetConsumerCommissionRate, "ChainId: %s", err.Error())
	}

	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSetConsumerCommissionRate, "ConsumerId: %s", err.Error())
	}

	_, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgSetConsumerCommissionRate, "ProviderAddr: %s", err.Error())
	}

	if msg.Rate.IsNegative() || msg.Rate.GT(math.LegacyOneDec()) {
		return errorsmod.Wrapf(ErrInvalidMsgSetConsumerCommissionRate, "consumer commission rate should be in the range [0, 1]")
	}

	return nil
}

// NewMsgCreateConsumer creates a new MsgCreateConsumer instance
func NewMsgCreateConsumer(signer string, chainId string, metadata ConsumerMetadata,
	initializationParameters *ConsumerInitializationParameters, powerShapingParameters *PowerShapingParameters) (*MsgCreateConsumer, error) {
	return &MsgCreateConsumer{
		Signer:                   signer,
		ChainId:                  chainId,
		Metadata:                 metadata,
		InitializationParameters: initializationParameters,
		PowerShapingParameters:   powerShapingParameters,
	}, nil
}

// Type implements the sdk.Msg interface.
func (msg MsgCreateConsumer) Type() string {
	return TypeMsgCreateConsumer
}

// Route implements the sdk.Msg interface.
func (msg MsgCreateConsumer) Route() string { return RouterKey }

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgCreateConsumer) ValidateBasic() error {
	if err := ValidateStringField("ChainId", msg.ChainId, cmttypes.MaxChainIDLen); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "ChainId: %s", err.Error())
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
func NewMsgUpdateConsumer(signer string, consumerId string, ownerAddress string, metadata *ConsumerMetadata,
	initializationParameters *ConsumerInitializationParameters, powerShapingParameters *PowerShapingParameters) (*MsgUpdateConsumer, error) {
	return &MsgUpdateConsumer{
		Signer:                   signer,
		ConsumerId:               consumerId,
		NewOwnerAddress:          ownerAddress,
		Metadata:                 metadata,
		InitializationParameters: initializationParameters,
		PowerShapingParameters:   powerShapingParameters,
	}, nil
}

// Type implements the sdk.Msg interface.
func (msg MsgUpdateConsumer) Type() string {
	return TypeMsgUpdateConsumer
}

// Route implements the sdk.Msg interface.
func (msg MsgUpdateConsumer) Route() string { return RouterKey }

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgUpdateConsumer) ValidateBasic() error {
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
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
func NewMsgRemoveConsumer(signer string, consumerId string, stopTime time.Time) (*MsgRemoveConsumer, error) {
	return &MsgRemoveConsumer{
		Signer:     signer,
		ConsumerId: consumerId,
		StopTime:   stopTime,
	}, nil
}

// Type implements the sdk.Msg interface.
func (msg MsgRemoveConsumer) Type() string {
	return TypeMsgRemoveConsumer
}

// Route implements the sdk.Msg interface.
func (msg MsgRemoveConsumer) Route() string { return RouterKey }

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgRemoveConsumer) ValidateBasic() error {
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
	}
	return nil
}

// Route implements the sdk.Msg interface.
func (msg MsgConsumerAddition) Route() string { return RouterKey }

// Route implements the sdk.Msg interface.
func (msg MsgConsumerModification) Route() string { return RouterKey }

// Route implements the sdk.Msg interface.
func (msg MsgConsumerRemoval) Route() string { return RouterKey }

//
// Validation methods
//

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

// TODO create UT
func ValidateTendermintHeader(header *ibctmtypes.Header) error {
	if header == nil {
		return fmt.Errorf("infraction block header cannot be nil")
	}

	if header.SignedHeader == nil {
		return fmt.Errorf("signed header in infraction block header cannot be nil")
	}

	if header.SignedHeader.Header == nil {
		return fmt.Errorf("invalid signed header in infraction block header, 'SignedHeader.Header' is nil")
	}

	if header.ValidatorSet == nil {
		return fmt.Errorf("invalid infraction block header, validator set is nil")
	}

	return nil
}

// ValidateConsumerId validates the provided consumer id and returns an error if it is not valid
func ValidateConsumerId(consumerId string) error {
	if strings.TrimSpace(consumerId) == "" {
		return errorsmod.Wrapf(ErrInvalidConsumerId, "consumer id cannot be blank")
	}

	// check that `consumerId` corresponds to a `uint64`
	_, err := strconv.ParseUint(consumerId, 10, 64)
	if err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerId, "consumer id (%s) cannot be parsed: %s", consumerId, err.Error())
	}

	return nil
}

// ValidateStringField validates that a string `field` satisfies the following properties:
//   - is not empty
//   - has at most `maxLength` characters
func ValidateStringField(nameOfTheField string, field string, maxLength int) error {
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

	if initializationParameters.SpawnTime.IsZero() {
		return errorsmod.Wrap(ErrInvalidConsumerInitializationParameters, "SpawnTime cannot be zero")
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
		return fmt.Errorf("hash is too long; got: %d, max: %d", len(hash), MaxHashLength)
	}
	return nil
}

func validateDeprecatedChainId(chainId string) error {
	if strings.TrimSpace(chainId) != "" {
		return fmt.Errorf("chainId is deprecated; use consumerId instead")
	}

	return nil
}
