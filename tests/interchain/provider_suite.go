package interchain

import (
	"context"
	"strconv"

	"cosmos/interchain-security/tests/interchain/chainsuite"

	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/stretchr/testify/suite"
)

type ProviderSuite struct {
	suite.Suite
	Provider       *chainsuite.Chain
	ValidatorNodes int
	ctx            context.Context
}

func (s *ProviderSuite) SetupSuite() {
	ctx, err := chainsuite.NewSuiteContext(&s.Suite)
	s.Require().NoError(err)
	s.ctx = ctx

	// create and start provider chain
	s.Provider, err = chainsuite.CreateChain(s.GetContext(), s.T(), chainsuite.GetProviderSpec(s.ValidatorNodes, providerModifiedGenesis()))
	s.Require().NoError(err)
}

func (s *ProviderSuite) GetContext() context.Context {
	s.Require().NotNil(s.ctx, "Tried to GetContext before it was set. SetupSuite must run first")
	return s.ctx
}

func providerModifiedGenesis() []cosmos.GenesisKV {
	return []cosmos.GenesisKV{
		cosmos.NewGenesisKV("app_state.staking.params.unbonding_time", chainsuite.ProviderUnbondingTime.String()),
		cosmos.NewGenesisKV("app_state.gov.params.voting_period", chainsuite.GovVotingPeriod.String()),
		cosmos.NewGenesisKV("app_state.gov.params.max_deposit_period", chainsuite.GovDepositPeriod.String()),
		cosmos.NewGenesisKV("app_state.gov.params.min_deposit.0.denom", chainsuite.Stake),
		cosmos.NewGenesisKV("app_state.gov.params.min_deposit.0.amount", strconv.Itoa(chainsuite.GovMinDepositAmount)),
		cosmos.NewGenesisKV("app_state.slashing.params.signed_blocks_window", strconv.Itoa(chainsuite.ProviderSlashingWindow)),
		cosmos.NewGenesisKV("app_state.slashing.params.downtime_jail_duration", chainsuite.DowntimeJailDuration.String()),
		cosmos.NewGenesisKV("app_state.slashing.params.slash_fraction_double_sign", chainsuite.SlashFractionDoubleSign),
		cosmos.NewGenesisKV("app_state.provider.params.slash_meter_replenish_period", chainsuite.ProviderReplenishPeriod),
		cosmos.NewGenesisKV("app_state.provider.params.slash_meter_replenish_fraction", chainsuite.ProviderReplenishFraction),
		cosmos.NewGenesisKV("app_state.provider.params.blocks_per_epoch", "1"),
		cosmos.NewGenesisKV("app_state.staking.params.max_validators", "1"),
	}
}
