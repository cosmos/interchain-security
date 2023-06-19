package integration_test

import (
	"testing"

	appConsumer "github.com/cosmos/interchain-security/v2/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/v2/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/v2/app/provider"
	intg "github.com/cosmos/interchain-security/v2/tests/integration"
	icstestingutils "github.com/cosmos/interchain-security/v2/testutil/ibc_testing"
	"github.com/stretchr/testify/suite"
)

// This file can be used as an example integration testing instance for any provider/consumer applications.
// In the case of this repo, we're testing the dummy provider/consumer applications,
// but to test any arbitrary app, one only needs to replicate this file and "specific_setup.go",
// then pass in the appropriate types and parameters to the suite. Note that provider and consumer
// applications types must implement the interfaces defined in /testutil/integration/interfaces.go to compile.

// Executes the standard group of ccv tests against a consumer and provider app.go implementation.
func TestCCVTestSuite(t *testing.T) {
	// Pass in concrete app types that implement the interfaces defined in /testutil/e2e/interfaces.go
	// IMPORTANT: the concrete app types passed in as type parameters here must match the
	// concrete app types returned by the relevant app initers.
	ccvSuite := intg.NewCCVTestSuite[*appProvider.App, *appConsumer.App](
		// Pass in ibctesting.AppIniters for provider and consumer.
		icstestingutils.ProviderAppIniter, icstestingutils.ConsumerAppIniter, []string{})

	// Run tests
	suite.Run(t, ccvSuite)
}

// Executes a standard suite of tests, against a democracy consumer app.go implementation.
func TestConsumerDemocracyCCVTestSuite(t *testing.T) {
	// Pass in concrete app type that implement the interface defined in /testutil/e2e/interfaces.go
	// IMPORTANT: the concrete app types passed in as type parameters here must match the
	// concrete app types returned by the relevant app initers.
	democSuite := intg.NewCCVTestSuite[*appProvider.App, *appConsumerDemocracy.App](
		// Pass in ibctesting.AppIniter for provider and democracy consumer.
		// TestRewardsDistribution needs to be skipped since the democracy specific distribution test is in ConsumerDemocracyTestSuite,
		// while this one tests consumer app without minter
		icstestingutils.ProviderAppIniter, icstestingutils.DemocracyConsumerAppIniter, []string{"TestRewardsDistribution"})

	// Run tests
	suite.Run(t, democSuite)
}

// Executes a specialized group of tests specific to a democracy consumer,
// against a democracy consumer app.go implementation.
func TestConsumerDemocracyTestSuite(t *testing.T) {
	// Pass in concrete app type that implement the interface defined in /testutil/e2e/interfaces.go
	// IMPORTANT: the concrete app type passed in as a type parameter here must match the
	// concrete app type returned by the relevant app initer.
	democSuite := intg.NewConsumerDemocracyTestSuite[*appConsumerDemocracy.App](
		// Pass in ibctesting.AppIniter for democracy consumer.
		icstestingutils.DemocracyConsumerAppIniter)

	// Run tests
	suite.Run(t, democSuite)
}
