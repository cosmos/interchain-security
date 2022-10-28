package types

import (
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
)

// staking message types
const (
	TypeMsgDesignateConsensusKeyForConsumerChain = "create_validator"
)

var (
	_ sdk.Msg                            = &MsgDesignateConsensusKeyForConsumerChain{}
	_ codectypes.UnpackInterfacesMessage = (*MsgDesignateConsensusKeyForConsumerChain)(nil)
)

// NewMsgDesignateConsensusKeyForConsumerChain creates a new MsgDesignateConsensusKeyForConsumerChain instance.
// Delegator address and validator address are the same.
func NewMsgDesignateConsensusKeyForConsumerChain() (*MsgDesignateConsensusKeyForConsumerChain, error) {

	return &MsgDesignateConsensusKeyForConsumerChain{}, nil
}

// Route implements the sdk.Msg interface.
func (msg MsgDesignateConsensusKeyForConsumerChain) Route() string { return RouterKey }

// Type implements the sdk.Msg interface.
func (msg MsgDesignateConsensusKeyForConsumerChain) Type() string {
	return TypeMsgDesignateConsensusKeyForConsumerChain
}

// GetSigners implements the sdk.Msg interface. It returns the address(es) that
// must sign over msg.GetSignBytes().
// If the validator address is not same as delegator's, then the validator must
// sign the msg as well.
func (msg MsgDesignateConsensusKeyForConsumerChain) GetSigners() []sdk.AccAddress {
	addrs := []sdk.AccAddress{}
	return addrs
}

// GetSignBytes returns the message bytes to sign over.
func (msg MsgDesignateConsensusKeyForConsumerChain) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(&msg)
	return sdk.MustSortJSON(bz)
}

// ValidateBasic implements the sdk.Msg interface.
func (msg MsgDesignateConsensusKeyForConsumerChain) ValidateBasic() error {

	return nil
}

// UnpackInterfaces implements UnpackInterfacesMessage.UnpackInterfaces
func (msg MsgDesignateConsensusKeyForConsumerChain) UnpackInterfaces(unpacker codectypes.AnyUnpacker) error {
	var pubKey cryptotypes.PubKey

	todo := &codectypes.Any{}
	// return unpacker.UnpackAny(msg.Pubkey, &pubKey)
	return unpacker.UnpackAny(todo, &pubKey)
}
