package types

import (
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
)

func NewCCValidator(address []byte, power int64) CrossChainValidator {
	return CrossChainValidator{
		Address: address,
		Power:   power,
	}
}

// NewHistoricalInfo will create a historical information struct from header and valset
// it will first sort valset before inclusion into historical info
func NewHistoricalInfo(header tmproto.Header) stakingtypes.HistoricalInfo {
	return stakingtypes.HistoricalInfo{
		Header: header,
		Valset: nil,
	}
}
