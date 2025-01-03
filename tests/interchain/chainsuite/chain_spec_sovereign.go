package chainsuite

import (
	"strconv"

	"github.com/strangelove-ventures/interchaintest/v8"
	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/strangelove-ventures/interchaintest/v8/ibc"
)

func GetSovereignSpec() *interchaintest.ChainSpec {
	fullNodes := FullNodeCount
	validators := 1

	return &interchaintest.ChainSpec{
		ChainName:     SovereignToConsumerChainID,
		NumFullNodes:  &fullNodes,
		NumValidators: &validators,
		ChainConfig: ibc.ChainConfig{
			ChainID:        SovereignToConsumerChainID,
			Bin:            SovereignBin,
			Denom:          Stake,
			Type:           CosmosChainType,
			GasPrices:      GasPrices + Stake,
			GasAdjustment:  2.0,
			TrustingPeriod: "336h",
			CoinType:       "118",
			Images: []ibc.DockerImage{
				{
					Repository: SouvereignImageName(),
					Version:    SouvereignImageVersion(),
					UIDGID:     "1025:1025",
				},
			},
			ConfigFileOverrides: map[string]any{
				"config/config.toml": DefaultConfigToml(),
			},
			Bech32Prefix:         Bech32PrefixConsumer,
			ModifyGenesis:        cosmos.ModifyGenesis(sovereignModifiedGenesis()),
			ModifyGenesisAmounts: DefaultGenesisAmounts(Stake),
		},
	}
}

func sovereignModifiedGenesis() []cosmos.GenesisKV {
	return []cosmos.GenesisKV{
		cosmos.NewGenesisKV("app_state.gov.params.voting_period", GovVotingPeriod.String()),
		cosmos.NewGenesisKV("app_state.gov.params.max_deposit_period", GovDepositPeriod.String()),
		cosmos.NewGenesisKV("app_state.gov.params.min_deposit.0.denom", Stake),
		cosmos.NewGenesisKV("app_state.gov.params.min_deposit.0.amount", strconv.Itoa(GovMinDepositAmount)),
	}
}
