package e2e_test

import (
	"testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/tests/e2e"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/stretchr/testify/suite"
)

// TODO: explanation of this file.

func TestCCVTestSuite(t *testing.T) {
	ccvSuite := e2e.NewCCVTestSuite(
		// TODO: Make this shiz below better
		simapp.NewProviderConsumerCoordinator,
		func(suite e2e.CCVTestSuite) e2e.ProviderKeeper {
			return &suite.GetProviderChain().App.(*appProvider.App).ProviderKeeper
		},
		func(suite e2e.CCVTestSuite) e2e.ConsumerKeeper {
			return &suite.GetConsumerChain().App.(*appConsumer.App).ConsumerKeeper
		},
	)
	suite.Run(t, ccvSuite)
}

// TODO: Run the gov enabled consumer against the standard suite of tests to make sure it
// sill passes

// TODO: Move stuff away from simapp package.

func TestConsumerDemocracyTestSuite(t *testing.T) {
	democSuite := e2e.NewConsumerDemocracyTestSuite(
		// TODO: Also make this shiz better
		simapp.NewProviderConsumerDemocracyCoordinator,
	)
	suite.Run(t, democSuite)
}
