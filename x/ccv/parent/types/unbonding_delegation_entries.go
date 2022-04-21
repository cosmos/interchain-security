package types

import (
	"github.com/cosmos/cosmos-sdk/codec"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

func MustUnmarshalUnbondingOp(cdc codec.BinaryCodec, value []byte) ccv.UnbondingOp {
	delegation, err := UnmarshalUnbondingOp(cdc, value)
	if err != nil {
		panic(err)
	}

	return delegation
}

func UnmarshalUnbondingOp(cdc codec.BinaryCodec, value []byte) (unbondingOp ccv.UnbondingOp, err error) {
	err = cdc.Unmarshal(value, &unbondingOp)
	return unbondingOp, err
}
