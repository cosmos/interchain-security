package e2e_test

import (
	"testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/stretchr/testify/suite"
)

// TODO: explanation of this file.

func TestCCVTestSuite(t *testing.T) {
	ccvSuite := NewCCVTestSuite(
		// TODO: Make this shiz below better
		simapp.NewProviderConsumerCoordinator,
		func(suite CCVTestSuite) providerKeeper {
			return &suite.providerChain.App.(*appProvider.App).ProviderKeeper
		},
		func(suite CCVTestSuite) consumerKeeper {
			return &suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper
		},
	)
	suite.Run(t, ccvSuite)
}

func TestConsumerDemocracyTestSuite(t *testing.T) {
	democSuite := NewConsumerDemocracyTestSuite(
		// TODO: Also make this shiz better
		simapp.NewProviderConsumerDemocracyCoordinator)
	suite.Run(t, democSuite)
}
