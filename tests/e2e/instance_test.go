package e2e_test

import (
	"testing"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/tests/e2e"
	e2etestutil "github.com/cosmos/interchain-security/testutil/e2e"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/stretchr/testify/suite"
)

// This file can be used as an example e2e testing instance for a particular application.
// In the case of this repo, we're testing the dummy provider/consumer applications,
// but to test any arbitrary app, you only need to replicate this file, and pass in the
// appropriate callback to the testing suites.

// Executes the standard group of ccv tests against an app.go implementation.
func TestCCVTestSuite(t *testing.T) {

	ccvSuite := e2e.NewCCVTestSuite(func(t *testing.T) (
		*ibctesting.Coordinator,
		*ibctesting.TestChain,
		*ibctesting.TestChain,
		e2etestutil.ProviderApp,
		e2etestutil.ConsumerApp,
	) {
		// Here we pass the concrete types that must implement the necessary interfaces
		// to be ran with e2e tests.
		// TODO: Move stuff away from simapp package.
		coord, prov, cons := simapp.NewProviderConsumerCoordinator(t)
		// TODO: search whole repo for casts to concrete app type after those have suppossedly been removed.
		return coord, prov, cons, prov.App.(*appProvider.App), cons.App.(*appConsumer.App)
	})
	suite.Run(t, ccvSuite)
}

// TODO: Run the gov enabled consumer against the standard suite of tests to make sure it
// sill passes

func TestConsumerDemocracyTestSuite(t *testing.T) {
	democSuite := e2e.NewConsumerDemocracyTestSuite(
		// TODO: Also make this shiz better
		simapp.NewProviderConsumerDemocracyCoordinator,
	)
	suite.Run(t, democSuite)
}
