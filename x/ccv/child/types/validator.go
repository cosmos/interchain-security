package types

import (
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	tmtypes "github.com/tendermint/tendermint/types"
)

// NewValidator returns a validator struct with consensus address derived
// from the given public key
func NewValidator(pubKey cryptotypes.PubKey, power int64) (Validator, error) {
	pkAny, err := codectypes.NewAnyWithValue(pubKey)
	if err != nil {
		return Validator{}, err
	}
	return Validator{
		ConsensusAddress: sdk.ConsAddress(pubKey.Address()).String(),
		ConsensusPubkey:  pkAny,
		VotingPower:      power,
	}, nil
}

func (v Validator) IsJailed() bool {
	return v.Jailed
}

func (v Validator) ToTmValidator() (tmtypes.Validator, error) {
	pk, err := v.ConsPubKey()
	if err != nil {
		return tmtypes.Validator{}, err
	}

	pkTM, err := cryptocodec.ToTmPubKeyInterface(pk)
	if err != nil {
		return tmtypes.Validator{}, err
	}
	return tmtypes.Validator{
		Address:     pkTM.Address().Bytes(),
		PubKey:      pkTM,
		VotingPower: v.VotingPower,
	}, nil
}

// ConsPubKey returns the validator PubKey as a cryptotypes.PubKey.
func (v Validator) ConsPubKey() (cryptotypes.PubKey, error) {
	pk, ok := v.ConsensusPubkey.GetCachedValue().(cryptotypes.PubKey)
	if !ok {
		return nil, sdkerrors.Wrapf(sdkerrors.ErrInvalidType, "expecting cryptotypes.PubKey, got %T", pk)
	}

	return pk, nil
}

// GetConsAddr extracts Consensus key address
func (v Validator) GetConsAddr() (sdk.ConsAddress, error) {
	pk, err := v.ConsPubKey()
	if err != nil {
		return nil, err
	}

	return sdk.ConsAddress(pk.Address()), nil
}

// UnpackInterfaces implements UnpackInterfacesMessage.UnpackInterfaces
func (v Validator) UnpackInterfaces(unpacker codectypes.AnyUnpacker) error {
	var pk cryptotypes.PubKey
	return unpacker.UnpackAny(v.ConsensusPubkey, &pk)
}

func FromTmValidator(val tmtypes.Validator) (Validator, error) {
	pk, err := cryptocodec.FromTmPubKeyInterface(val.PubKey)
	if err != nil {
		return Validator{}, err
	}
	return NewValidator(pk, val.VotingPower)
}

func MustParseConsAdrr(addr string) sdk.ConsAddress {
	if addr == "" {
		return nil
	}
	out, err := sdk.ConsAddressFromBech32(addr)
	if err != nil {
		panic(err)
	}

	return out
}
