package interchain

import (
	"context"
	"cosmos/interchain-security/tests/interchain/chainsuite"

	"github.com/stretchr/testify/suite"
)

type ProviderSuite struct {
	suite.Suite
	Provider *chainsuite.Chain
	ctx      context.Context
}

func (s *ProviderSuite) SetupSuite() {
	ctx, err := chainsuite.NewSuiteContext(&s.Suite)
	s.Require().NoError(err)
	s.ctx = ctx

	// create and start provider chain
	s.Provider, err = chainsuite.CreateProviderChain(s.GetContext(), s.T(), chainsuite.GetProviderSpec())
	s.Require().NoError(err)
}

func (s *ProviderSuite) GetContext() context.Context {
	s.Require().NotNil(s.ctx, "Tried to GetContext before it was set. SetupSuite must run first")
	return s.ctx
}
