package types

import (
	"encoding/json"
	"fmt"
	"strconv"
	"strings"
	"time"

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
	TypeMsgCreateConsumer             = "create_consumer"
	TypeMsgUpdateConsumer             = "update_consumer"
	TypeMsgRemoveConsumer             = "remove_consumer"
	TypeMsgOptIn                      = "opt_in"
	TypeMsgOptOut                     = "opt_out"
	TypeMsgSetConsumerCommissionRate  = "set_consumer_commission_rate"
)

var (
	_ sdk.Msg = (*MsgAssignConsumerKey)(nil)
	_ sdk.Msg = (*MsgChangeRewardDenoms)(nil)
	_ sdk.Msg = (*MsgSubmitConsumerMisbehaviour)(nil)
	_ sdk.Msg = (*MsgSubmitConsumerDoubleVoting)(nil)
	_ sdk.Msg = (*MsgCreateConsumer)(nil)
	_ sdk.Msg = (*MsgUpdateConsumer)(nil)
	_ sdk.Msg = (*MsgRemoveConsumer)(nil)
	_ sdk.Msg = (*MsgConsumerAddition)(nil)
	_ sdk.Msg = (*MsgConsumerModification)(nil)
	_ sdk.Msg = (*MsgConsumerRemoval)(nil)
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
	_ sdk.HasValidateBasic = (*MsgConsumerAddition)(nil)
	_ sdk.HasValidateBasic = (*MsgConsumerModification)(nil)
	_ sdk.HasValidateBasic = (*MsgConsumerRemoval)(nil)
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
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
	}
	_, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return ErrInvalidProviderAddress
	}
	if msg.ConsumerKey == "" {
		return ErrInvalidConsumerConsensusPubKey
	}
	if _, _, err := ParseConsumerKeyFromJson(msg.ConsumerKey); err != nil {
		return ErrInvalidConsumerConsensusPubKey
	}
	return nil
}

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
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
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

	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
	}

	return nil
}

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

// NewMsgCreateConsumer creates a new MsgCreateConsumer instance
func NewMsgCreateConsumer(signer string, chainId string, metadata ConsumerMetadata,
	initializationParameters ConsumerInitializationParameters, powerShapingParameters PowerShapingParameters) (*MsgCreateConsumer, error) {
	return &MsgCreateConsumer{
		Signer:                   signer,
		ChainId:                  chainId,
		Metadata:                 &metadata,
		InitializationParameters: &initializationParameters,
		PowerShapingParameters:   &powerShapingParameters,
	}, nil
}

// Type implements the sdk.Msg interface.
func (msg MsgCreateConsumer) Type() string {
	return TypeMsgCreateConsumer
}

// Route implements the sdk.Msg interface.
func (msg MsgCreateConsumer) Route() string { return RouterKey }

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgCreateConsumer) ValidateBasic() error {
	// add checks
	// TODO (PERMISSIONLESS)
	return nil
}

// Type implements the sdk.Msg interface.
func (msg MsgCreateConsumer) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
func (msg MsgCreateConsumer) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.Signer)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// NewMsgUpdateConsumer creates a new MsgUpdateConsumer instance
func NewMsgUpdateConsumer(signer string, consumerId string, ownerAddress string, metadata ConsumerMetadata,
	initializationParameters ConsumerInitializationParameters, powerShapingParameters PowerShapingParameters) (*MsgUpdateConsumer, error) {
	return &MsgUpdateConsumer{
		Signer:                   signer,
		ConsumerId:               consumerId,
		OwnerAddress:             ownerAddress,
		Metadata:                 &metadata,
		InitializationParameters: &initializationParameters,
		PowerShapingParameters:   &powerShapingParameters,
	}, nil
}

// Type implements the sdk.Msg interface.
func (msg MsgUpdateConsumer) Type() string {
	return TypeMsgUpdateConsumer
}

// Route implements the sdk.Msg interface.
func (msg MsgUpdateConsumer) Route() string { return RouterKey }

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgUpdateConsumer) ValidateBasic() error {
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
	}

	// TODO (PERMISSIONLESS): validate update record
	err := ValidatePSSFeatures(msg.PowerShapingParameters.Top_N, msg.PowerShapingParameters.ValidatorsPowerCap)
	if err != nil {
		return errorsmod.Wrapf(ErrInvalidUpdateRecord, "invalid PSS features: %s", err.Error())
	}

	return nil
}

// Type implements the sdk.Msg interface.
func (msg MsgUpdateConsumer) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
func (msg MsgUpdateConsumer) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.Signer)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// NewMsgRemoveConsumer creates a new MsgRemoveConsumer instance
func NewMsgRemoveConsumer(signer string, consumerId string, stopTime time.Time) (*MsgRemoveConsumer, error) {
	return &MsgRemoveConsumer{
		Authority:  signer,
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

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgRemoveConsumer) ValidateBasic() error {
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
	}
	return nil
}

// Type implements the sdk.Msg interface.
func (msg MsgRemoveConsumer) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
func (msg MsgRemoveConsumer) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.Authority)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// Route implements the sdk.Msg interface.
func (msg MsgConsumerAddition) Route() string { return RouterKey }

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgConsumerAddition) ValidateBasic() error {
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

// Type implements the sdk.Msg interface.
func (msg MsgConsumerAddition) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
func (msg MsgConsumerAddition) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.Authority)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// Route implements the sdk.Msg interface.
func (msg MsgConsumerModification) Route() string { return RouterKey }

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgConsumerModification) ValidateBasic() error {
	if strings.TrimSpace(msg.ChainId) == "" {
		return ErrBlankConsumerChainID
	}

	err := ValidatePSSFeatures(msg.Top_N, msg.ValidatorsPowerCap)
	if err != nil {
		return errorsmod.Wrapf(ErrInvalidConsumerModificationProposal, "invalid PSS features: %s", err.Error())
	}

	return nil
}

// Type implements the sdk.Msg interface.
func (msg MsgConsumerModification) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
func (msg MsgConsumerModification) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.Authority)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// Route implements the sdk.Msg interface.
func (msg MsgConsumerRemoval) Route() string { return RouterKey }

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgConsumerRemoval) ValidateBasic() error {
	if strings.TrimSpace(msg.ChainId) == "" {
		return errorsmod.Wrap(ErrInvalidConsumerRemoval, "consumer chain id must not be blank")
	}

	if msg.StopTime.IsZero() {
		return errorsmod.Wrap(ErrInvalidConsumerRemoval, "spawn time cannot be zero")
	}
	return nil
}

// Type implements the sdk.Msg interface.
func (msg MsgConsumerRemoval) GetSignBytes() []byte {
	bz := ccvtypes.ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
func (msg MsgConsumerRemoval) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.Authority)
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
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
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
	}
	_, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return ErrInvalidProviderAddress
	}

	if msg.ConsumerKey != "" {
		if _, _, err := ParseConsumerKeyFromJson(msg.ConsumerKey); err != nil {
			return ErrInvalidConsumerConsensusPubKey
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
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
	}
	_, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return ErrInvalidProviderAddress
	}
	return nil
}

// NewMsgSetConsumerCommissionRate creates a new MsgSetConsumerCommissionRate msg instance.
func NewMsgSetConsumerCommissionRate(consumerId string, commission math.LegacyDec, providerValidatorAddress sdk.ValAddress, signer string) *MsgSetConsumerCommissionRate {
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

func (msg MsgSetConsumerCommissionRate) ValidateBasic() error {
	if err := ValidateConsumerId(msg.ConsumerId); err != nil {
		return err
	}
	_, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return ErrInvalidProviderAddress
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
