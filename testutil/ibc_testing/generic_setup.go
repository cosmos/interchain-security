package ibc_testing

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	e2eutil "github.com/cosmos/interchain-security/testutil/e2e"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
)

// Contains generic setup code for running e2e tests against a provider, consumer,
// and/or democracy consumer app.go implementation. You should not need to modify or replicate this file
// to run e2e tests against your app.go implementations!

var (
	FirstConsumerChainID = ibctesting.GetChainID(2)
	provChainID          = ibctesting.GetChainID(1)
	democConsumerChainID = ibctesting.GetChainID(5000)
)

type ConsumerBundle struct {
	Chain        *ibctesting.TestChain
	App          e2eutil.ConsumerApp
	Path         *ibctesting.Path
	TransferPath *ibctesting.Path
}

// TODO: wrapper around ibc testing path to have consumer and provider syntax?
// or too big of a refactor?

// GetCtx returns the context for the ConsumerBundle
func (cb ConsumerBundle) GetCtx() sdk.Context {
	return cb.Chain.GetContext()
}

// GetKeeper returns the keeper for the ConsumerBundle
func (cb ConsumerBundle) GetKeeper() consumerkeeper.Keeper {
	return cb.App.GetConsumerKeeper()
}

// AddProvider adds a new provider chain to the coordinator and returns the test chain and app type
func AddProvider[T e2eutil.ProviderApp](coordinator *ibctesting.Coordinator, t *testing.T, appIniter ibctesting.AppIniter) (
	*ibctesting.TestChain, T) {

	provider := ibctesting.NewTestChain(t, coordinator, appIniter, provChainID)
	coordinator.Chains[provChainID] = provider

	return provider, provider.App.(T)
}

// AddDemocracyConsumer adds a new democ consumer chain to the coordinator and returns the test chain and app type
func AddDemocracyConsumer[T e2eutil.DemocConsumerApp](coordinator *ibctesting.Coordinator, t *testing.T,
	appIniter ibctesting.AppIniter) (*ibctesting.TestChain, T) {

	democConsumer := ibctesting.NewTestChain(t, coordinator, appIniter, democConsumerChainID)
	coordinator.Chains[democConsumerChainID] = democConsumer

	return democConsumer, democConsumer.App.(T)
}

// AddConsumers adds new consumer chains to the coordinator and returns the test chains and app types
// The new consumers are initialized with the valset of the existing provider chain.
//
// This method must be called after AddProvider.
func AddConsumers[T e2eutil.ConsumerApp](coordinator *ibctesting.Coordinator,
	t *testing.T, numConsumers int, appIniter ibctesting.AppIniter) map[string]*ConsumerBundle {

	providerChain := coordinator.GetChain(provChainID)

	// Instantiate specified number of consumer bundles, add chain to coordinator, and return bundles
	consumerBundles := make(map[string]*ConsumerBundle)
	for i := 0; i < numConsumers; i++ {
		chainID := ibctesting.GetChainID(i + 2)
		testChain := ibctesting.NewTestChainWithValSet(t, coordinator,
			appIniter, chainID, providerChain.Vals, providerChain.Signers)

		coordinator.Chains[chainID] = testChain
		consumerBundles[chainID] = &ConsumerBundle{
			Chain: testChain,
			App:   testChain.App.(T),
		}
	}
	return consumerBundles
}
