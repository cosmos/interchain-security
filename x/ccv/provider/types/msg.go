package types

import (
	"encoding/json"
	"errors"
	"fmt"
	"strings"

	clienttypes "github.com/cosmos/ibc-go/v9/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v9/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"

	tmtypes "github.com/cometbft/cometbft/proto/tendermint/types"
	cmttypes "github.com/cometbft/cometbft/types"

	ccvtypes "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

const (
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

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgAssignConsumerKey) ValidateBasic() error {
	if err := validateDeprecatedChainId(msg.ChainId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgAssignConsumerKey, "ChainId: %s", err.Error())
	}

	if err := ccvtypes.ValidateConsumerId(msg.ConsumerId); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgAssignConsumerKey, "ConsumerId: %s", err.Error())
	}

	if err := validateProviderAddress(msg.ProviderAddr, msg.Signer); err != nil {
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
	}
	return nil
}

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
	allowlistedRewardDenoms *AllowlistedRewardDenoms, infractionParameters *InfractionParameters,
) (*MsgCreateConsumer, error) {
	return &MsgCreateConsumer{
		Submitter:                submitter,
		ChainId:                  chainId,
		Metadata:                 metadata,
		InitializationParameters: initializationParameters,
		PowerShapingParameters:   powerShapingParameters,
		AllowlistedRewardDenoms:  allowlistedRewardDenoms,
		InfractionParameters:     infractionParameters,
	}, nil
}

// IsReservedChainId returns true if the specific chain id is reserved and cannot be used by other consumer chains
func IsReservedChainId(chainId string) bool {
	// With permissionless ICS, we can have multiple consumer chains with the exact same chain id.
	// However, as we already have the Neutron and Stride Top N chains running, as a first step we would like to
	// prevent permissionless chains from re-using the chain ids of Neutron and Stride. Note that this is just a
	// preliminary measure that will be removed later on as part of:
	// TODO (#2242): find a better way of ignoring past misbehaviors
	return chainId == "neutron-1" || chainId == "stride-1"
}

// ValidateChainId validates that the chain id is valid and is not reserved.
// Can be called for the `MsgUpdateConsumer.NewChainId` field as well, so this method takes the `field` as an argument
// to return more appropriate error messages in case the validation fails.
func ValidateChainId(field string, chainId string) error {
	if err := ValidateStringField(field, chainId, cmttypes.MaxChainIDLen); err != nil {
		return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "%s: %s", field, err.Error())
	}

	if IsReservedChainId(chainId) {
		return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "cannot use a reserved chain id")
	}

	return nil
}

// ValidateBasic implements the sdk.HasValidateBasic interface.
func (msg MsgCreateConsumer) ValidateBasic() error {
	if err := ValidateChainId("ChainId", msg.ChainId); err != nil {
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
			return errors.New("cannot create a Top N chain through `MsgCreateConsumer`; " +
				"first create the chain and then use `MsgUpdateConsumer` to make the chain Top N")
		}
		if err := ValidatePowerShapingParameters(*msg.PowerShapingParameters); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "PowerShapingParameters: %s", err.Error())
		}
	}

	if msg.InfractionParameters != nil {
		if err := ValidateInfractionParameters(*msg.InfractionParameters); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "InfractionParameters: %s", err.Error())
		}
	}

	if msg.AllowlistedRewardDenoms != nil {
		if err := ValidateAllowlistedRewardDenoms(*msg.AllowlistedRewardDenoms); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgCreateConsumer, "AllowlistedRewardDenoms: %s", err.Error())
		}
	}

	return nil
}

// NewMsgUpdateConsumer creates a new MsgUpdateConsumer instance
func NewMsgUpdateConsumer(owner, consumerId, ownerAddress string, metadata *ConsumerMetadata,
	initializationParameters *ConsumerInitializationParameters, powerShapingParameters *PowerShapingParameters,
	allowlistedRewardDenoms *AllowlistedRewardDenoms, newChainId string, infractionParameters *InfractionParameters,
) (*MsgUpdateConsumer, error) {
	return &MsgUpdateConsumer{
		Owner:                    owner,
		ConsumerId:               consumerId,
		NewOwnerAddress:          ownerAddress,
		Metadata:                 metadata,
		InitializationParameters: initializationParameters,
		PowerShapingParameters:   powerShapingParameters,
		AllowlistedRewardDenoms:  allowlistedRewardDenoms,
		NewChainId:               newChainId,
		InfractionParameters:     infractionParameters,
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

	if msg.InfractionParameters != nil {
		if err := ValidateInfractionParameters(*msg.InfractionParameters); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgUpdateConsumer, "InfractionParameters: %s", err.Error())
		}
	}

	if msg.AllowlistedRewardDenoms != nil {
		if err := ValidateAllowlistedRewardDenoms(*msg.AllowlistedRewardDenoms); err != nil {
			return errorsmod.Wrapf(ErrInvalidMsgUpdateConsumer, "AllowlistedRewardDenoms: %s", err.Error())
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

// ValidateHeaderForConsumerDoubleVoting validates Tendermint light client header
// for consumer double voting evidence.
//
// TODO create unit test
func ValidateHeaderForConsumerDoubleVoting(header *ibctmtypes.Header) error {
	if header == nil {
		return errors.New("infraction block header cannot be nil")
	}

	if header.SignedHeader == nil {
		return errors.New("signed header in infraction block header cannot be nil")
	}

	if header.SignedHeader.Header == nil {
		return errors.New("invalid signed header in infraction block header, 'SignedHeader.Header' is nil")
	}

	if header.ValidatorSet == nil {
		return errors.New("invalid infraction block header, validator set is nil")
	}

	return nil
}

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
	if err := ValidateConsAddressList(powerShapingParameters.Prioritylist, MaxValidatorCount); err != nil {
		return errorsmod.Wrapf(ErrInvalidPowerShapingParameters, "Prioritylist: %s", err.Error())
	}

	return nil
}

// ValidateAllowlistedRewardDenoms validates the provided allowlisted reward denoms
func ValidateAllowlistedRewardDenoms(allowlistedRewardDenoms AllowlistedRewardDenoms) error {
	if len(allowlistedRewardDenoms.Denoms) > MaxAllowlistedRewardDenomsPerChain {
		return errorsmod.Wrapf(ErrInvalidAllowlistedRewardDenoms, "More than %d denoms", MaxAllowlistedRewardDenomsPerChain)
	}

	for _, denom := range allowlistedRewardDenoms.Denoms {
		if err := ccvtypes.ValidateIBCDenom(denom); err != nil {
			return errorsmod.Wrapf(ErrInvalidAllowlistedRewardDenoms, "Invalid denom (%s): %s", denom, err.Error())
		}
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

	if err := ccvtypes.ValidateConnectionIdentifier(initializationParameters.ConnectionId); err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerInitializationParameters, "ConnectionId: %s", err.Error())
	}

	return nil
}

// ValidateInfractionParameters validates that all the provided infraction parameters are in the expected range
func ValidateInfractionParameters(initializationParameters InfractionParameters) error {
	if initializationParameters.DoubleSign != nil {
		if initializationParameters.DoubleSign.JailDuration < 0 {
			return errorsmod.Wrap(ErrInvalidConsumerInfractionParameters, "DoubleSign.JailDuration cannot be negative")
		}
		if err := ccvtypes.ValidateFraction(initializationParameters.DoubleSign.SlashFraction); err != nil {
			return errorsmod.Wrapf(ErrInvalidConsumerInfractionParameters, "DoubleSign.SlashFraction: %s", err.Error())
		}
	}

	if initializationParameters.Downtime != nil {
		if initializationParameters.Downtime.JailDuration < 0 {
			return errorsmod.Wrap(ErrInvalidConsumerInfractionParameters, "Downtime.JailDuration cannot be negative")
		}
		if err := ccvtypes.ValidateFraction(initializationParameters.Downtime.SlashFraction); err != nil {
			return errorsmod.Wrapf(ErrInvalidConsumerInfractionParameters, "Downtime.SlashFraction: %s", err.Error())
		}
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
	if err != nil {
		return fmt.Errorf("invalid ValAddress (%s)", addr)
	}

	// Check that the provider validator address and the signer address are the same
	accAddr := sdk.AccAddress(valAddr.Bytes()).String()
	if accAddr != signer {
		return fmt.Errorf("ValAddress converted to AccAddress (%s) must match the signer address (%s)", accAddr, signer)
	}

	return nil
}

func ValidateInitialHeight(initialHeight clienttypes.Height, chainID string) error {
	revision := clienttypes.ParseChainID(chainID)
	if initialHeight.RevisionNumber != revision {
		return fmt.Errorf("chain ID (%s) doesn't match revision number (%d)", chainID, initialHeight.RevisionNumber)
	}
	return nil
}
