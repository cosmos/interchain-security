package e2e_test

import (
	"testing"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/tests/e2e"
	e2etestutil "github.com/cosmos/interchain-security/testutil/e2e"
	ibctestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
	"github.com/stretchr/testify/suite"
)

// This file can be used as an example e2e testing instance for any provider/consumer applications.
// In the case of this repo, we're testing the dummy provider/consumer applications,
// but to test any arbitrary app, one only needs to replicate this file and "specific_setup.go",
// then pass in the appropriate callback to the testing suites. Note that any provider/consumer
// applications must implement the interfaces defined in /testutil/e2e/interfaces.go to compile.

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
			// Instantiate the test coordinator.
			coordinator := ibctesting.NewCoordinator(t, 0)

			// Add provider to coordinator, store returned test chain and app.
			// Concrete provider app type is passed to the generic function here.
			provider, providerApp := ibctestingutils.AddProvider[*appProvider.App](
				coordinator, t, ibctestingutils.ProviderAppIniter)

			// Add specified number of consumers to coordinator, store returned test chains and apps.
			// Concrete consumer app type is passed to the generic function here.
			consumers, consumerApps := ibctestingutils.AddConsumers[*appConsumer.App](
				coordinator, t, 1, ibctestingutils.ConsumerAppIniter)

			// Pass variables to suite.
			// TODO: accept multiple consumers here
			return coordinator, provider, consumers[0], providerApp, consumerApps[0]
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
			// Instantiate the test coordinator
			coordinator := ibctesting.NewCoordinator(t, 0)

			// Add single democracy consumer to coordinator, store returned test chain and app.
			democConsumer, democConsumerApp := ibctestingutils.AddDemocracyConsumer[*appConsumerDemocracy.App](
				coordinator, t, ibctestingutils.DemocracyConsumerAppIniter)

			// Pass variables to suite.
			return coordinator, democConsumer, democConsumerApp
		},
	)
	suite.Run(t, democSuite)
}
