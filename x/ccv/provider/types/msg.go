package types

import (
	"encoding/json"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
)

// provider message types
const (
	TypeMsgAssignConsumerKey           = "assign_consumer_key"
	TypeMsgRegisterConsumerRewardDenom = "register_consumer_reward_denom"
)

var _ sdk.Msg = &MsgAssignConsumerKey{}

// NewMsgAssignConsumerKey creates a new MsgAssignConsumerKey instance.
// Delegator address and validator address are the same.
func NewMsgAssignConsumerKey(chainID string, providerValidatorAddress sdk.ValAddress,
	consumerConsensusPubKey string,
) (*MsgAssignConsumerKey, error) {
	return &MsgAssignConsumerKey{
		ChainId:      chainID,
		ProviderAddr: providerValidatorAddress.String(),
		ConsumerKey:  consumerConsensusPubKey,
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

// NewMsgRegisterConsumerRewardDenom returns a new MsgRegisterConsumerRewardDenom with a sender and
// a funding amount.
func NewMsgRegisterConsumerRewardDenom(denom string, depositor sdk.AccAddress) *MsgRegisterConsumerRewardDenom {
	return &MsgRegisterConsumerRewardDenom{
		Denom:     denom,
		Depositor: depositor.String(),
	}
}

// Route returns the MsgRegisterConsumerRewardDenom message route.
func (msg MsgRegisterConsumerRewardDenom) Route() string { return ModuleName }

// Type returns the MsgRegisterConsumerRewardDenom message type.
func (msg MsgRegisterConsumerRewardDenom) Type() string { return TypeMsgRegisterConsumerRewardDenom }

// GetSigners returns the signer addresses that are expected to sign the result
// of GetSignBytes.
func (msg MsgRegisterConsumerRewardDenom) GetSigners() []sdk.AccAddress {
	depoAddr, err := sdk.AccAddressFromBech32(msg.Depositor)
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{depoAddr}
}

// GetSignBytes returns the raw bytes for a MsgRegisterConsumerRewardDenom message that
// the expected signer needs to sign.
func (msg MsgRegisterConsumerRewardDenom) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// ValidateBasic performs basic MsgRegisterConsumerRewardDenom message validation.
func (msg MsgRegisterConsumerRewardDenom) ValidateBasic() error {
	if !sdk.NewCoin(msg.Denom, sdk.NewInt(0)).IsValid() {
		return ErrInvalidConsumerRewardDenom
	}
	_, err := sdk.AccAddressFromBech32(msg.Depositor)
	if err != nil {
		return ErrInvalidDepositorAddress
	}

	return nil
}
