package chainsuite

import (
	"time"

	"github.com/strangelove-ventures/interchaintest/v8/testutil"

	sdkmath "cosmossdk.io/math"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
)

const (
	ProviderImageName         = "ghcr.io/cosmos/interchain-security"
	ProviderImageVersion      = "v6.1.0"
	ProviderBin               = "interchain-security-pd"
	ProviderBech32Prefix      = "cosmos"
	ProviderValOperPrefix     = "cosmosvaloper"
	ProviderChainID           = "ics-provider"
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
	// ValidatorCount is set to 2, so we have one active and one inactive (i.e., outside the active set) validator.
	// Note that the provider has at most 1 validator (see `chain_spec_provider.go`).
	ValidatorCount    = 2
	FullNodeCount     = 0
	ChainSpawnWait    = 155 * time.Second
	CosmosChainType   = "cosmos"
	GovModuleAddress  = "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn"
	TestWalletsNumber = 15 // Ensure that test accounts are used in a way that maintains the mutual independence of tests
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
