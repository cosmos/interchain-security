package chainsuite

import (
	"github.com/cosmos/interchaintest/v10/chain/cosmos"
	"github.com/cosmos/interchaintest/v10/ibc"

	"github.com/cosmos/interchaintest/v10"
)

func GetProviderSpec(validatorCount int, modifiedGenesis []cosmos.GenesisKV) *interchaintest.ChainSpec {
	fullNodes := FullNodeCount
	validators := validatorCount

	return &interchaintest.ChainSpec{
		Name:          ProviderChainID,
		NumFullNodes:  &fullNodes,
		NumValidators: &validators,
		Version:       ProviderImageVersion(),
		ChainConfig: ibc.ChainConfig{
			Type:           CosmosChainType,
			Bin:            ProviderBin,
			Bech32Prefix:   ProviderBech32Prefix,
			Denom:          Stake,
			GasPrices:      GasPrices + Stake,
			GasAdjustment:  2.0,
			TrustingPeriod: "504h",
			ConfigFileOverrides: map[string]any{
				"config/config.toml": DefaultConfigToml(),
			},
			Images: []ibc.DockerImage{{
				Repository: ProviderImageName(),
				UIDGID:     "1025:1025",
			}},
			ModifyGenesis:        cosmos.ModifyGenesis(modifiedGenesis),
			ModifyGenesisAmounts: DefaultGenesisAmounts(Stake),
		},
	}
}
