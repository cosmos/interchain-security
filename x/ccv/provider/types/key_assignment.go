package types

import (
	"fmt"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

// A validator's consensus address on the provider chain
type ProviderConsAddr struct {
	sdk.ConsAddress
}

// A validator's assigned consensus address for a consumer chain
type ConsumerConsAddr struct {
	sdk.ConsAddress
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
		if err := sdk.VerifyAddressFormat(e.ProviderAddr); err != nil {
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
		if err := sdk.VerifyAddressFormat(e.ProviderAddr); err != nil {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, fmt.Sprintf("invalid provider address: %s", e.ProviderAddr))
		}
		if err := sdk.VerifyAddressFormat(e.ConsumerAddr); err != nil {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, fmt.Sprintf("invalid consumer address: %s", e.ConsumerAddr))
		}
	}
	for _, e := range consumerAddrsToPrune {
		if strings.TrimSpace(e.ChainId) == "" {
			return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, "consumer chain id must not be blank")
		}
		// Don't check e.vscid, it's an unsigned integer
		for _, a := range e.ConsumerAddrs.Addresses {
			if err := sdk.VerifyAddressFormat(a); err != nil {
				return sdkerrors.Wrap(ccvtypes.ErrInvalidGenesis, fmt.Sprintf("invalid consumer address: %s", a))
			}
		}
	}
	return nil
}
