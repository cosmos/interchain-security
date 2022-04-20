package types

import (
	"github.com/cosmos/cosmos-sdk/codec"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

func MustUnmarshalUnbondingDelegationEntry(cdc codec.BinaryCodec, value []byte) ccv.UnbondingOp {
	delegation, err := UnmarshalUnbondingDelegationEntry(cdc, value)
	if err != nil {
		panic(err)
	}

	return delegation
}

func UnmarshalUnbondingDelegationEntry(cdc codec.BinaryCodec, value []byte) (unbondingOp ccv.UnbondingOp, err error) {
	err = cdc.Unmarshal(value, &unbondingOp)
	return unbondingOp, err
}
