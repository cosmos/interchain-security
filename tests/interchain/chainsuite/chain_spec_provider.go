package chainsuite

import (
	"strconv"

	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/strangelove-ventures/interchaintest/v8/ibc"

	"github.com/strangelove-ventures/interchaintest/v8"
)

func GetProviderSpec() *interchaintest.ChainSpec {
	fullNodes := FullNodeCount
	validators := ValidatorCount

	return &interchaintest.ChainSpec{
		Name:          ProviderChainID,
		NumFullNodes:  &fullNodes,
		NumValidators: &validators,
		Version:       ProviderImageVersion,
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
				Repository: ProviderImageName,
				UIDGID:     "1025:1025",
			}},
			ModifyGenesis:        cosmos.ModifyGenesis(providerModifiedGenesis()),
			ModifyGenesisAmounts: DefaultGenesisAmounts(Stake),
		},
	}
}

func providerModifiedGenesis() []cosmos.GenesisKV {
	return []cosmos.GenesisKV{
		cosmos.NewGenesisKV("app_state.staking.params.unbonding_time", ProviderUnbondingTime.String()),
		cosmos.NewGenesisKV("app_state.gov.params.voting_period", GovVotingPeriod.String()),
		cosmos.NewGenesisKV("app_state.gov.params.max_deposit_period", GovDepositPeriod.String()),
		cosmos.NewGenesisKV("app_state.gov.params.min_deposit.0.denom", Stake),
		cosmos.NewGenesisKV("app_state.gov.params.min_deposit.0.amount", strconv.Itoa(GovMinDepositAmount)),
		cosmos.NewGenesisKV("app_state.slashing.params.signed_blocks_window", strconv.Itoa(ProviderSlashingWindow)),
		cosmos.NewGenesisKV("app_state.slashing.params.downtime_jail_duration", DowntimeJailDuration.String()),
		cosmos.NewGenesisKV("app_state.provider.params.slash_meter_replenish_period", ProviderReplenishPeriod),
		cosmos.NewGenesisKV("app_state.provider.params.slash_meter_replenish_fraction", ProviderReplenishFraction),
		cosmos.NewGenesisKV("app_state.provider.params.blocks_per_epoch", "1"),
	}
}
