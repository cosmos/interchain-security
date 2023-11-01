package types

import (
	"encoding/json"
	"strings"
	"time"

	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// provider message types
const (
	TypeMsgAssignConsumerKey = "assign_consumer_key"
)

var (
	_ sdk.Msg = (*MsgAssignConsumerKey)(nil)
	_ sdk.Msg = (*MsgConsumerAddition)(nil)
	_ sdk.Msg = (*MsgConsumerRemoval)(nil)

	_ sdk.HasValidateBasic = (*MsgAssignConsumerKey)(nil)
	_ sdk.HasValidateBasic = (*MsgConsumerAddition)(nil)
	_ sdk.HasValidateBasic = (*MsgConsumerRemoval)(nil)
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
	bz := ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgAssignConsumerKey) ValidateBasic() error {
	if strings.TrimSpace(msg.ChainId) == "" {
		return ErrBlankConsumerChainID
	}
	// It is possible to assign keys for consumer chains that are not yet approved.
	// This can only be done by a signing validator, but it is still sensible
	// to limit the chainID size to prevent abuse.
	// TODO: In future, a mechanism will be added to limit assigning keys to chains
	// which are approved or pending approval, only.
	if 128 < len(msg.ChainId) {
		return ErrBlankConsumerChainID
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

// NewMsgConsumerAddition creates a new MsgConsumerAddition instance.
func NewMsgConsumerAddition(signer, chainID string,
	initialHeight clienttypes.Height, genesisHash, binaryHash []byte,
	spawnTime time.Time,
	consumerRedistributionFraction string,
	blocksPerDistributionTransmission int64,
	distributionTransmissionChannel string,
	historicalEntries int64,
	ccvTimeoutPeriod time.Duration,
	transferTimeoutPeriod time.Duration,
	unbondingPeriod time.Duration) *MsgConsumerAddition {
	return &MsgConsumerAddition{
		ChainId:                           chainID,
		InitialHeight:                     initialHeight,
		GenesisHash:                       genesisHash,
		BinaryHash:                        binaryHash,
		SpawnTime:                         spawnTime,
		ConsumerRedistributionFraction:    consumerRedistributionFraction,
		BlocksPerDistributionTransmission: blocksPerDistributionTransmission,
		DistributionTransmissionChannel:   distributionTransmissionChannel,
		HistoricalEntries:                 historicalEntries,
		CcvTimeoutPeriod:                  ccvTimeoutPeriod,
		TransferTimeoutPeriod:             transferTimeoutPeriod,
		UnbondingPeriod:                   unbondingPeriod,
		Signer:                            signer,
	}
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
// If the validator address is not same as delegator's, then the validator must
// sign the msg as well.
func (msg *MsgConsumerAddition) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.Signer)
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

	if strings.TrimSpace(msg.ChainId) == "" {
		return errorsmod.Wrap(ErrInvalidConsumerAdditionProposal, "consumer chain id must not be blank")
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

// NewMsgConsumerRemoval creates a new MsgConsumerRemoval instance
func NewMsgConsumerRemoval(signer string) *MsgConsumerRemoval {
	//@bermuell: TODO finsh implementation!
	return &MsgConsumerRemoval{}
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
