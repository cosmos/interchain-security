package params

import (
	"github.com/cosmos/cosmos-sdk/codec"
	"github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/x/auth/tx"
)

// MakeTestEncodingConfig creates an EncodingConfig for an amino based test configuration.
func MakeTestEncodingConfig() EncodingConfig {
	amino := codec.NewLegacyAmino()
	interfaceRegistry := types.NewInterfaceRegistry()
	chainCodec := codec.NewProtoCodec(interfaceRegistry)
	txCfg := tx.NewTxConfig(chainCodec, tx.DefaultSignModes)

	return EncodingConfig{
		InterfaceRegistry: interfaceRegistry,
		Codec:             chainCodec,
		TxConfig:          txCfg,
		Amino:             amino,
	}
}
