package chainsuite

import (
	"time"

	"github.com/strangelove-ventures/interchaintest/v8/testutil"

	sdkmath "cosmossdk.io/math"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
)

const (
	ImageName                 = "ghcr.io/cosmos/interchain-security"
	ImageVersion              = "v6.1.0"
	Bech32Prefix              = "cosmos"
	ValOperPrefix             = "cosmosvaloper"
	ProviderBin               = "interchain-security-pd"
	ProviderChainID           = "ics-provider"
	ConsumerBin               = "interchain-security-cd"
	ConsumerChainID           = "ics-consumer"
	Stake                     = "stake"
	DowntimeJailDuration      = 10 * time.Second
	ProviderSlashingWindow    = 10
	ProviderUnbondingTime     = 10 * time.Second
	ProviderReplenishPeriod   = "2s"
	ProviderReplenishFraction = "1.00"
	GovMinDepositAmount       = 1000
	GovMinDepositString       = "1000" + Stake
	GovDepositPeriod          = 10 * time.Second
	GovVotingPeriod           = 15 * time.Second
	GasPrices                 = "0.005"
	UpgradeDelta              = 30
	SlashingWindowConsumer    = 20
	CommitTimeout             = 2 * time.Second
	TotalValidatorFunds       = 11_000_000_000
	ValidatorFunds            = 30_000_000
	ValidatorCount            = 1
	FullNodeCount             = 0
	ChainSpawnWait            = 155 * time.Second
	CosmosChainType           = "cosmos"
	GovModuleAddress          = "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn"
	TestWalletsNumber         = 15 // Ensure that test accounts are used in a way that maintains the mutual independence of tests
	// relayer params
	RelayerImageName    = "ghcr.io/informalsystems/hermes"
	RelayerImageVersion = "v1.8.0"
)

func DefaultConfigToml() testutil.Toml {
	configToml := make(testutil.Toml)
	consensusToml := make(testutil.Toml)
	consensusToml["timeout_commit"] = CommitTimeout
	configToml["consensus"] = consensusToml
	configToml["block_sync"] = false
	configToml["fast_sync"] = false
	return configToml
}

func DefaultGenesisAmounts(denom string) func(i int) (sdktypes.Coin, sdktypes.Coin) {
	return func(i int) (sdktypes.Coin, sdktypes.Coin) {
		return sdktypes.Coin{
				Denom:  denom,
				Amount: sdkmath.NewInt(TotalValidatorFunds),
			}, sdktypes.Coin{
				Denom:  denom,
				Amount: sdkmath.NewInt(ValidatorFunds),
			}
	}
}
