package interchain

import (
	"context"
	"cosmos/interchain-security/tests/interchain/chainsuite"
	"time"

	"github.com/strangelove-ventures/interchaintest/v8"
	"github.com/stretchr/testify/suite"
)

type ConsumerSuite struct {
	suite.Suite
	Provider *chainsuite.Chain
	Consumer *chainsuite.Chain
	Relayer  *chainsuite.Relayer
	ctx      context.Context
}

func (s *ConsumerSuite) SetupSuite() {
	ctx, err := chainsuite.NewSuiteContext(&s.Suite)
	s.Require().NoError(err)
	s.ctx = ctx

	// create and start provider chain
	s.Provider, err = chainsuite.CreateProviderChain(s.GetContext(), s.T(), chainsuite.GetProviderSpec())
	s.Require().NoError(err)

	// setup hermes relayer
	relayer, err := chainsuite.NewRelayer(s.GetContext(), s.T())
	s.Require().NoError(err)
	s.Relayer = relayer
	err = relayer.SetupChainKeys(s.GetContext(), s.Provider)
	s.Require().NoError(err)

	// create and start consumer chain
	s.Consumer, err = s.Provider.AddConsumerChain(s.GetContext(), relayer, chainsuite.ConsumerChainID, s.GetConsumerSpec(ctx))
	s.Require().NoError(err)
	//s.Require().NoError(s.Provider.UpdateAndVerifyStakeChange(s.GetContext(), s.Consumer, relayer, 1_000_000, 0))

}

func (s *ConsumerSuite) GetContext() context.Context {
	s.Require().NotNil(s.ctx, "Tried to GetContext before it was set. SetupSuite must run first")
	return s.ctx
}

func (s *ConsumerSuite) GetConsumerSpec(ctx context.Context) *interchaintest.ChainSpec {
	spawnTime := time.Now().Add(time.Second * 30)
	proposalMsg := msgCreateConsumer(chainsuite.ConsumerChainID, consumerInitParamsTemplate(&spawnTime), powerShapingParamsTemplate(), chainsuite.GovModuleAddress)
	return chainsuite.GetConsumerSpec(ctx, s.Provider, proposalMsg, []int{0})
}

