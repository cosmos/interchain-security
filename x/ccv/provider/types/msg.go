package types

import (
	"strings"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
)

// provider message types
const (
	TypeMsgAssignConsensusPublicKeyToConsumerChain = "assign_consensus_public_key_to_consumer_chain"
)

var (
	_ sdk.Msg                            = &MsgAssignConsensusPublicKeyToConsumerChain{}
	_ codectypes.UnpackInterfacesMessage = (*MsgAssignConsensusPublicKeyToConsumerChain)(nil)
)

// NewMsgAssignConsensusPublicKeyToConsumerChain creates a new MsgAssignConsensusPublicKeyToConsumerChain instance.
// Delegator address and validator address are the same.
func NewMsgAssignConsensusPublicKeyToConsumerChain(chainID string, providerValidatorAddress sdk.ValAddress,
	consumerConsensusPubKey cryptotypes.PubKey) (*MsgAssignConsensusPublicKeyToConsumerChain, error) {
	var keyAsAny *codectypes.Any
	if consumerConsensusPubKey != nil {
		var err error
		if keyAsAny, err = codectypes.NewAnyWithValue(consumerConsensusPubKey); err != nil {
			return nil, err
		}
	}
	return &MsgAssignConsensusPublicKeyToConsumerChain{
		ChainId:                  chainID,
		ProviderValidatorAddress: providerValidatorAddress.String(),
		ConsumerConsensusPubKey:  keyAsAny,
	}, nil
}

// Route implements the sdk.Msg interface.
func (msg MsgAssignConsensusPublicKeyToConsumerChain) Route() string { return RouterKey }

// Type implements the sdk.Msg interface.
func (msg MsgAssignConsensusPublicKeyToConsumerChain) Type() string {
	return TypeMsgAssignConsensusPublicKeyToConsumerChain
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
// If the validator address is not same as delegator's, then the validator must
// sign the msg as well.
func (msg MsgAssignConsensusPublicKeyToConsumerChain) GetSigners() []sdk.AccAddress {
	valAddr, err := sdk.ValAddressFromBech32(msg.ProviderValidatorAddress)
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{valAddr.Bytes()}
}

// GetSignBytes returns the message bytes to sign over.
func (msg MsgAssignConsensusPublicKeyToConsumerChain) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgAssignConsensusPublicKeyToConsumerChain) ValidateBasic() error {
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
	if msg.ProviderValidatorAddress == "" {
		return ErrEmptyValidatorAddr
	}
	if msg.ConsumerConsensusPubKey == nil {
		return ErrInvalidConsumerConsensusPubKey
	}
	return nil
}

// UnpackInterfaces implements UnpackInterfacesMessage.UnpackInterfaces
func (msg MsgAssignConsensusPublicKeyToConsumerChain) UnpackInterfaces(unpacker codectypes.AnyUnpacker) error {
	var pubKey cryptotypes.PubKey
	return unpacker.UnpackAny(msg.ConsumerConsensusPubKey, &pubKey)
}
