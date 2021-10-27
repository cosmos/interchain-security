package types

import (
	"github.com/cosmos/cosmos-sdk/codec"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

func MustUnmarshalUnbondingDelegationEntry(cdc codec.BinaryCodec, value []byte) ccv.UnbondingDelegationEntry {
	delegation, err := UnmarshalUnbondingDelegationEntry(cdc, value)
	if err != nil {
		panic(err)
	}

	return delegation
}

func UnmarshalUnbondingDelegationEntry(cdc codec.BinaryCodec, value []byte) (ubde ccv.UnbondingDelegationEntry, err error) {
	err = cdc.Unmarshal(value, &ubde)
	return ubde, err
}
