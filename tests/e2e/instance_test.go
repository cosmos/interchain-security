package e2e_test

import (
	"testing"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/tests/e2e"
	e2etestutil "github.com/cosmos/interchain-security/testutil/e2e"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/stretchr/testify/suite"
)

// This file can be used as an example e2e testing instance for any provider/consumer applications.
// In the case of this repo, we're testing the dummy provider/consumer applications,
// but to test any arbitrary app, you only need to replicate this file, and pass in the
// appropriate callback to the testing suites. Note that any provider/consumer applications
// must implement the interfaces defined in /testutil/e2e/interfaces.go

// Executes the standard group of ccv tests against a consumer and provider app.go implementation.
func TestCCVTestSuite(t *testing.T) {

	ccvSuite := e2e.NewCCVTestSuite(
		func(t *testing.T) (
			*ibctesting.Coordinator,
			*ibctesting.TestChain,
			*ibctesting.TestChain,
			e2etestutil.ProviderApp,
			e2etestutil.ConsumerApp,
		) {
			// Here we pass the concrete types that must implement the necessary interfaces
			// to be ran with e2e tests.
			coord, prov, cons := simapp.NewProviderConsumerCoordinator(t)
			return coord, prov, cons, prov.App.(*appProvider.App), cons.App.(*appConsumer.App)
		},
	)
	suite.Run(t, ccvSuite)
}

// TODO: Run the gov enabled consumer against the standard suite of tests: https://github.com/cosmos/interchain-security/issues/397

// Executes a specialized group of tests specific to a democracy consumer, against a democracy consumer app.go implementation.
func TestConsumerDemocracyTestSuite(t *testing.T) {
	democSuite := e2e.NewConsumerDemocracyTestSuite(
		func(t *testing.T) (
			*ibctesting.Coordinator,
			*ibctesting.TestChain,
			e2etestutil.DemocConsumerApp,
		) {
			// Here we pass the concrete types that must implement the necessary interfaces
			// to be ran with e2e tests.
			coord, _, cons := simapp.NewProviderConsumerDemocracyCoordinator(t)
			return coord, cons, cons.App.(*appConsumerDemocracy.App)
		},
	)
	suite.Run(t, democSuite)
}
