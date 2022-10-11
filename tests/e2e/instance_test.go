package e2e_test

import (
	"testing"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/tests/e2e"
	keepertestutil "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/stretchr/testify/suite"
)

// TODO: explanation of this file.

func TestCCVTestSuite(t *testing.T) {

	ccvSuite := e2e.NewCCVTestSuite(func(t *testing.T) (
		*ibctesting.Coordinator,
		*ibctesting.TestChain,
		*ibctesting.TestChain,
		keepertestutil.ProviderApp,
		keepertestutil.ConsumerApp,
	) {
		coord, prov, cons := simapp.NewProviderConsumerCoordinator(t)
		return coord, prov, cons, prov.App.(*appProvider.App), cons.App.(*appConsumer.App)
	})
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
