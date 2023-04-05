package app

import (
	"github.com/cosmos/cosmos-sdk/codec"
	"github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/std"
	"github.com/cosmos/cosmos-sdk/x/auth/tx"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/app/consumer-democracy"
	appparams "github.com/cosmos/interchain-security/app/params"
	appProvider "github.com/cosmos/interchain-security/app/provider"
)

// MakeEncodingConfig creates an EncodingConfig for an amino based test configuration.
func MakeEncodingConfigProviderApp() appparams.EncodingConfig {
	amino := codec.NewLegacyAmino()
	interfaceRegistry := types.NewInterfaceRegistry()
	ircodec := codec.NewProtoCodec(interfaceRegistry)
	txCfg := tx.NewTxConfig(ircodec, tx.DefaultSignModes)

	encodingConfig := appparams.EncodingConfig{
		InterfaceRegistry: interfaceRegistry,
		Codec:             ircodec,
		TxConfig:          txCfg,
		Amino:             amino,
	}

	std.RegisterLegacyAminoCodec(encodingConfig.Amino)
	std.RegisterInterfaces(encodingConfig.InterfaceRegistry)
	appProvider.ModuleBasics.RegisterLegacyAminoCodec(encodingConfig.Amino)
	appProvider.ModuleBasics.RegisterInterfaces(encodingConfig.InterfaceRegistry)
	return encodingConfig
}

func MakeEncodingConfigConsumerApp() appparams.EncodingConfig {
	amino := codec.NewLegacyAmino()
	interfaceRegistry := types.NewInterfaceRegistry()
	ircodec := codec.NewProtoCodec(interfaceRegistry)
	txCfg := tx.NewTxConfig(ircodec, tx.DefaultSignModes)

	encodingConfig := appparams.EncodingConfig{
		InterfaceRegistry: interfaceRegistry,
		Codec:             ircodec,
		TxConfig:          txCfg,
		Amino:             amino,
	}

	std.RegisterLegacyAminoCodec(encodingConfig.Amino)
	std.RegisterInterfaces(encodingConfig.InterfaceRegistry)
	appConsumer.ModuleBasics.RegisterLegacyAminoCodec(encodingConfig.Amino)
	appConsumer.ModuleBasics.RegisterInterfaces(encodingConfig.InterfaceRegistry)
	return encodingConfig
}

func MakeEncodingConfigDemocracyConsumerApp() appparams.EncodingConfig {
	amino := codec.NewLegacyAmino()
	interfaceRegistry := types.NewInterfaceRegistry()
	ircodec := codec.NewProtoCodec(interfaceRegistry)
	txCfg := tx.NewTxConfig(ircodec, tx.DefaultSignModes)

	encodingConfig := appparams.EncodingConfig{
		InterfaceRegistry: interfaceRegistry,
		Codec:             ircodec,
		TxConfig:          txCfg,
		Amino:             amino,
	}

	std.RegisterLegacyAminoCodec(encodingConfig.Amino)
	std.RegisterInterfaces(encodingConfig.InterfaceRegistry)
	appConsumerDemocracy.ModuleBasics.RegisterLegacyAminoCodec(encodingConfig.Amino)
	appConsumerDemocracy.ModuleBasics.RegisterInterfaces(encodingConfig.InterfaceRegistry)
	return encodingConfig
}
