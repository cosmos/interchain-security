package interchain

import (
	"context"
	"cosmos/interchain-security/tests/interchain/chainsuite"
	"strconv"
	"time"

	sdkmath "cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v9/modules/core/02-client/types"
	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/strangelove-ventures/interchaintest/v8/ibc"
	"github.com/stretchr/testify/suite"
)

type ProviderConsumersSuite struct {
	suite.Suite
	Provider  *chainsuite.Chain
	Sovereign *chainsuite.Chain
	Consumer  *chainsuite.Chain
	Relayer   *chainsuite.Relayer
	ctx       context.Context
}

func (s *ProviderConsumersSuite) SetupSuite() {
	ctx, err := chainsuite.NewSuiteContext(&s.Suite)
	s.Require().NoError(err)
	s.ctx = ctx

	// create and start provider chain
	s.Provider, err = chainsuite.CreateChain(s.GetContext(), s.T(), chainsuite.GetProviderSpec(1, provConsumerModifiedGenesis()))
	s.Require().NoError(err)

	// create and start sovereign chain that will later changeover to consumer
	s.Sovereign, err = chainsuite.CreateChain(s.GetContext(), s.T(), chainsuite.GetSovereignSpec())
	s.Require().NoError(err)

	// setup hermes relayer
	relayer, err := chainsuite.NewRelayer(s.GetContext(), s.T())
	s.Require().NoError(err)
	s.Relayer = relayer

	// create and start consumer chain
	spawnTime := time.Now().Add(time.Hour)
	initParams := consumerInitParamsTemplate(&spawnTime)
	initParams.InitialHeight = clienttypes.Height{RevisionNumber: clienttypes.ParseChainID(chainsuite.ConsumerChainID), RevisionHeight: 1}
	proposalMsg := msgCreateConsumer(chainsuite.ConsumerChainID, initParams, powerShapingParamsTemplate(), nil, chainsuite.ProviderGovModuleAddress)
	s.Consumer, err = s.Provider.AddConsumerChain(s.GetContext(), relayer, chainsuite.GetConsumerSpec(s.GetContext(), s.Provider, proposalMsg))
	s.Require().NoError(err)

	s.Require().NoError(relayer.SetupChainKeys(s.GetContext(), s.Provider))
	s.Require().NoError(relayer.SetupChainKeys(s.GetContext(), s.Sovereign))
	s.Require().NoError(relayer.SetupChainKeys(s.GetContext(), s.Consumer))
	s.Require().NoError(relayer.RestartRelayer(s.GetContext()))

	// confirm that tx on consumer can not be send before consumer and provider are connected
	err = s.Consumer.SendFunds(ctx, chainsuite.ValidatorMoniker, ibc.WalletAmount{
		Amount:  sdkmath.NewInt(1000),
		Denom:   s.Consumer.Config().Denom,
		Address: s.Consumer.RelayerWallet.FormattedAddress(),
	})
	s.Require().Error(err)
	s.Require().Contains(err.Error(), "tx contains unsupported message types")
	// connect consumer and provider
	s.Require().NoError(s.Relayer.ConnectProviderConsumer(s.GetContext(), s.Provider, s.Consumer))
	s.Require().NoError(relayer.RestartRelayer(s.GetContext()))
	s.Require().NoError(s.Provider.UpdateAndVerifyStakeChange(s.GetContext(), s.Consumer, s.Relayer, 1_000_000, 0))
	providerInfo, err := s.Consumer.GetProviderInfo(s.GetContext())
	s.Require().NoError(err)
	s.Require().Equal("connection-0", providerInfo.Provider.ConnectionID)

	// build test wallets for consumer after ics connection is established and bank send txs are allowed
	testWallets, err := chainsuite.SetupTestWallets(ctx, s.Consumer.CosmosChain, chainsuite.TestWalletsNumber)
	s.Require().NoError(err)
	s.Consumer.TestWallets = testWallets
}

func (s *ProviderConsumersSuite) GetContext() context.Context {
	s.Require().NotNil(s.ctx, "Tried to GetContext before it was set. SetupSuite must run first")
	return s.ctx
}

func provConsumerModifiedGenesis() []cosmos.GenesisKV {
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
