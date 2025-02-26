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
	SovereignBin               = "interchain-security-sd"
	ConsumerBin                = "interchain-security-cdd"
	ProviderChainID            = "ics-provider"
	SovereignToConsumerChainID = "ics-sovereign-consumer"
	ConsumerChainID            = "ics-consumer"
	ProviderBech32Prefix       = "cosmos"
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
	BlocksPerDistribution      = 5
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
	return getImageVersion("PROVIDER_IMAGE_TAG")
}

func ProviderImageName() string {
	return getImageName("PROVIDER_IMAGE_NAME")
}

func SouvereignImageVersion() string {
	return getImageVersion("SOVEREIGN_IMAGE_TAG")
}

func SouvereignImageName() string {
	return getImageName("SOVEREIGN_IMAGE_NAME")
}

func ConsumerImageVersion() string {
	return getImageVersion("CONSUMER_IMAGE_TAG")
}

func ConsumerImageName() string {
	return getImageName("CONSUMER_IMAGE_NAME")
}

func getImageName(imgName string) string {
	imageName := os.Getenv(imgName)
	if imageName == "" {
		imageName = "ghcr.io/cosmos/interchain-security"
	}

	return imageName
}

func getImageVersion(imgVersion string) string {
	imageVersion := os.Getenv(imgVersion)
	if imageVersion == "" {
		imageVersion = "latest"
	}

	return imageVersion
}
