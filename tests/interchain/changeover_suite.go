package interchain

import (
	"context"
	"cosmos/interchain-security/tests/interchain/chainsuite"
	"strconv"

	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/stretchr/testify/suite"
)

type ChangeoverSuite struct {
	suite.Suite
	Provider *chainsuite.Chain
	Consumer *chainsuite.Chain
	Relayer  *chainsuite.Relayer
	ctx      context.Context
}

func (s *ChangeoverSuite) SetupSuite() {
	ctx, err := chainsuite.NewSuiteContext(&s.Suite)
	s.Require().NoError(err)
	s.ctx = ctx

	// create and start provider chain
	s.Provider, err = chainsuite.CreateChain(s.GetContext(), s.T(), chainsuite.GetProviderSpec(1, provChangeoverModifiedGenesis()))
	s.Require().NoError(err)

	// create and start sovereign chain that will later changeover to consumer
	s.Consumer, err = chainsuite.CreateChain(s.GetContext(), s.T(), chainsuite.GetSovereignSpec())
	s.Require().NoError(err)

	// setup hermes relayer
	relayer, err := chainsuite.NewRelayer(s.GetContext(), s.T())
	s.Require().NoError(err)
	s.Relayer = relayer

	err = relayer.SetupChainKeys(s.GetContext(), s.Provider)
	s.Require().NoError(err)
	s.Require().NoError(relayer.RestartRelayer(ctx))

	err = relayer.SetupChainKeys(s.GetContext(), s.Consumer)
	s.Require().NoError(err)
	s.Require().NoError(relayer.RestartRelayer(ctx))
}

func (s *ChangeoverSuite) GetContext() context.Context {
	s.Require().NotNil(s.ctx, "Tried to GetContext before it was set. SetupSuite must run first")
	return s.ctx
}

func provChangeoverModifiedGenesis() []cosmos.GenesisKV {
	return []cosmos.GenesisKV{
		cosmos.NewGenesisKV("app_state.staking.params.unbonding_time", (chainsuite.ProviderUnbondingTime * 10000000).String()),
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
