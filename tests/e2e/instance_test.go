package e2e_test

import (
	"testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/tests/e2e"
	ibctestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
	"github.com/stretchr/testify/suite"
)

// This file can be used as an example e2e testing instance for any provider/consumer applications.
// In the case of this repo, we're testing the dummy provider/consumer applications,
// but to test any arbitrary app, one only needs to replicate this file and "specific_setup.go",
// then pass in the appropriate types and parameters to the suite. Note that provider consumer
// applications types must implement the interfaces defined in /testutil/e2e/interfaces.go to compile.

// Executes the standard group of ccv tests against a consumer and provider app.go implementation.
func TestCCVTestSuite(t *testing.T) {

	// Pass in concrete app types that implement the interfaces defined in /testutil/e2e/interfaces.go
	ccvSuite := e2e.NewCCVTestSuite[*appProvider.App, *appConsumer.App](
		// Pass in ibctesting.AppIniters for provider and consumer.
		ibctestingutils.ProviderAppIniter, ibctestingutils.ConsumerAppIniter)

	// Run tests
	suite.Run(t, ccvSuite)
}

// TODO: Run the gov enabled consumer against the standard suite of tests: https://github.com/cosmos/interchain-security/issues/397

// Executes a specialized group of tests specific to a democracy consumer,
// against a democracy consumer app.go implementation.
func TestConsumerDemocracyTestSuite(t *testing.T) {

	// Pass in concrete app type that implement the interface defined in /testutil/e2e/interfaces.go
	democSuite := e2e.NewConsumerDemocracyTestSuite[*appConsumerDemocracy.App](
		// Pass in ibctesting.AppIniter for democracy consumer.
		ibctestingutils.DemocracyConsumerAppIniter)

	// Run tests
	suite.Run(t, democSuite)
}
