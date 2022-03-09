package types

import (
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	abci "github.com/tendermint/tendermint/abci/types"
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

// UnpackInterfaces implements UnpackInterfacesMessage.UnpackInterfaces
func (v Validators) UnpackInterfaces(c codectypes.AnyUnpacker) error {
	for i := range v {
		if err := v[i].UnpackInterfaces(c); err != nil {
			return err
		}
	}
	return nil
}

type Validators []Validator

func (vals Validators) GetValset() (tmtypes.ValidatorSet, error) {
	valset := tmtypes.ValidatorSet{}
	for _, val := range vals {
		valTm, err := val.ToTmValidator()
		if err != nil {
			return valset, err
		}
		valset.Validators = append(valset.Validators, &valTm)
	}
	return valset, nil
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

func (v Validator) ToChange() (change abci.ValidatorUpdate, err error) {
	tmVal, err := v.ToTmValidator()
	if err != nil {
		return
	}
	change = tmtypes.TM2PB.ValidatorUpdate(&tmVal)
	return
}
