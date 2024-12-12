package chainsuite

import (
	"os"
	"time"

	"github.com/strangelove-ventures/interchaintest/v8/testutil"

	sdkmath "cosmossdk.io/math"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
)

const (
	ProviderBin                = "interchain-security-pd"
	ProviderBech32Prefix       = "cosmos"
	ProviderValOperPrefix      = "cosmosvaloper"
	ProviderChainID            = "ics-provider"
	SovereignToConsumerChainID = "ics-sovereign-consumer"
	SovereignBin               = "interchain-security-sd"
	Bech32PrefixConsumer       = "consumer"
	Stake                      = "stake"
	DowntimeJailDuration       = 10 * time.Second
	SlashFractionDoubleSign    = "0.05"
	ProviderSlashingWindow     = 10
	ProviderUnbondingTime      = 10 * time.Second
	ProviderReplenishPeriod    = "2s"
	ProviderReplenishFraction  = "1.00"
	GovMinDepositAmount        = 1000
	GovMinDepositString        = "1000" + Stake
	GovDepositPeriod           = 10 * time.Second
	GovVotingPeriod            = 15 * time.Second
	GasPrices                  = "0.005"
	UpgradeDelta               = 30
	SlashingWindowConsumer     = 20
	CommitTimeout              = 2 * time.Second
	TotalValidatorFunds        = 11_000_000_000
	ValidatorFunds             = 30_000_000
	FullNodeCount              = 0
	ChainSpawnWait             = 155 * time.Second
	CosmosChainType            = "cosmos"
	ProviderGovModuleAddress   = "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn"
	ConsumerGovModuleAddress   = "consumer10d07y265gmmuvt4z0w9aw880jnsr700jlh7295"
	TestWalletsNumber          = 20
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
	// Returns an amount of funds per validator, so validator with val index 0 has the most funds, then validator 1, then validator 2, etc.
	return func(i int) (sdktypes.Coin, sdktypes.Coin) {
		return sdktypes.Coin{
				Denom:  denom,
				Amount: sdkmath.NewInt(TotalValidatorFunds / int64(i+1)),
			}, sdktypes.Coin{
				Denom:  denom,
				Amount: sdkmath.NewInt(ValidatorFunds / int64(i+1)),
			}
	}
}

func ProviderImageVersion() string {
	providerImageVersion := os.Getenv("PROVIDER_IMAGE_TAG")
	if providerImageVersion == "" {
		providerImageVersion = "latest"
	}

	return providerImageVersion
}

func ProviderImageName() string {
	providerImageName := os.Getenv("PROVIDER_IMAGE_NAME")
	if providerImageName == "" {
		providerImageName = "ghcr.io/cosmos/interchain-security"
	}

	return providerImageName
}

func SouvereignImageVersion() string {
	souvereignImageVersion := os.Getenv("SOUVEREIGN_IMAGE_TAG")
	if souvereignImageVersion == "" {
		souvereignImageVersion = "latest"
	}

	return souvereignImageVersion
}

func SouvereignImageName() string {
	souvereignImageName := os.Getenv("SOUVEREIGN_IMAGE_NAME")
	if souvereignImageName == "" {
		souvereignImageName = "ghcr.io/cosmos/interchain-security"
	}

	return souvereignImageName
}
