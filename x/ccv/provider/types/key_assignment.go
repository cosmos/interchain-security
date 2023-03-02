package types

import (
	"fmt"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

// NewProviderConsAddress creates a new ProviderConsAddress,
// a validator's consensus address on the provider chain.
func NewProviderConsAddress(addr sdk.ConsAddress) ProviderConsAddress {
	return ProviderConsAddress{
		Address: addr,
	}
}

func (p *ProviderConsAddress) ToSdkConsAddr() sdk.ConsAddress {
	return sdk.ConsAddress(p.Address)
}

// String implements the Stringer interface for ProviderConsAddress,
// in the same format as sdk.ConsAddress
func (p *ProviderConsAddress) String() string {
	return p.ToSdkConsAddr().String()
}

// NewConsumerConsAddress creates a new ConsumerConsAddress,
// a validator's assigned consensus address for a consumer chain.
// Note this type is for type safety within provider code, consumer code uses normal sdk.ConsAddress,
// since there's no notion of provider vs consumer address.
func NewConsumerConsAddress(addr sdk.ConsAddress) ConsumerConsAddress {
	return ConsumerConsAddress{
		Address: addr,
	}
}

func (c *ConsumerConsAddress) ToSdkConsAddr() sdk.ConsAddress {
	return sdk.ConsAddress(c.Address)
}

// String implements the Stringer interface for ConsumerConsAddress,
// in the same format as sdk.ConsAddress
func (c *ConsumerConsAddress) String() string {
	return c.ToSdkConsAddr().String()
}

// KeyAssignmentValidateBasic validates all the genesis state for key assignment
// This is a utility. Key Assignment does not define any new proto types, but
// has a lot of nested data.
func KeyAssignmentValidateBasic(
	assignedKeys []ValidatorConsumerPubKey,
	byConsumerAddrs []ValidatorByConsumerAddr,
	consumerAddrsToPrune []ConsumerAddrsToPrune,
) error {
	for _, e := range assignedKeys {
		if strings.TrimSpace(e.ChainId) == "" {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, "consumer chain id must not be blank")
		}
		if err := sdk.VerifyAddressFormat(e.ProviderAddr.ToSdkConsAddr()); err != nil {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, fmt.Sprintf("invalid provider address: %s", e.ProviderAddr))
		}
		if e.ConsumerKey == nil {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, fmt.Sprintf("invalid consumer key: %s", e.ConsumerKey))
		}
	}
	for _, e := range byConsumerAddrs {
		if strings.TrimSpace(e.ChainId) == "" {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, "consumer chain id must not be blank")
		}
		if err := sdk.VerifyAddressFormat(e.ProviderAddr.ToSdkConsAddr()); err != nil {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, fmt.Sprintf("invalid provider address: %s", e.ProviderAddr))
		}
		if err := sdk.VerifyAddressFormat(e.ConsumerAddr.ToSdkConsAddr()); err != nil {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, fmt.Sprintf("invalid consumer address: %s", e.ConsumerAddr))
		}
	}
	for _, e := range consumerAddrsToPrune {
		if strings.TrimSpace(e.ChainId) == "" {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, "consumer chain id must not be blank")
		}
		// Don't check e.vscid, it's an unsigned integer
		for _, a := range e.ConsumerAddrs.Addresses {
			if err := sdk.VerifyAddressFormat(a.ToSdkConsAddr()); err != nil {
				return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, fmt.Sprintf("invalid consumer address: %s", a))
			}
		}
	}
	return nil
}
