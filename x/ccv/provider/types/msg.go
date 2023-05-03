package types

import (
	"crypto/ed25519"
	"encoding/base64"
	"fmt"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
)

// provider message types
const (
	TypeMsgAssignConsumerKey = "assign_consumer_key"
)

var (
	_ sdk.Msg = &MsgAssignConsumerKey{}
)

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

	pubKeyBytes, err := base64.StdEncoding.DecodeString(msg.ConsumerKey)
	if err != nil {
		return err
	}

	// make sure consumer key is correct ed25519 size
	if len(pubKeyBytes) != ed25519.PublicKeySize {
		return fmt.Errorf(
			"invalid consumer pub key len, got: %d, expected: %d", len(msg.ConsumerKey), ed25519.PublicKeySize,
		)
	}
	return nil
}
