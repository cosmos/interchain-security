package ibc_testing

import (
	"testing"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	"github.com/cosmos/interchain-security/testutil/e2e"
)

// Contains generic setup code for running e2e tests against a provider, consumer,
// and/or democracy consumer app.go implementation. You should not need to modify or replicate this file
// to run e2e tests against your app.go implementations!

var (
	provChainID          = ibctesting.GetChainID(1)
	democConsumerChainID = ibctesting.GetChainID(2)
)

// AddProvider adds a new provider chain to the coordinator and returns the test chain and app type
func AddProvider[T e2e.ProviderApp](coordinator *ibctesting.Coordinator, t *testing.T, appIniter ibctesting.AppIniter) (
	*ibctesting.TestChain, T) {

	provider := ibctesting.NewTestChain(t, coordinator, appIniter, provChainID)
	coordinator.Chains[provChainID] = provider

	return provider, provider.App.(T)
}

// AddDemocracyConsumer adds a new democ consumer chain to the coordinator and returns the test chain and app type
func AddDemocracyConsumer[T e2e.DemocConsumerApp](coordinator *ibctesting.Coordinator, t *testing.T,
	appIniter ibctesting.AppIniter) (*ibctesting.TestChain, T) {

	democConsumer := ibctesting.NewTestChain(t, coordinator, appIniter, democConsumerChainID)
	coordinator.Chains[democConsumerChainID] = democConsumer

	return democConsumer, democConsumer.App.(T)
}

// AddConsumers adds new consumer chains to the coordinator and returns the test chains and app types
// The new consumers are initialized with the valset of the existing provider chain.
//
// This method must be called after AddProvider.
func AddConsumers[T e2e.ConsumerApp](coordinator *ibctesting.Coordinator,
	t *testing.T, numConsumers int, appIniter ibctesting.AppIniter) ([]*ibctesting.TestChain, []T) {

	providerChain := coordinator.GetChain(provChainID)

	// Instantiate specified number of consumers, add them to coordinator, and returned chain/app slices
	consumerChains := []*ibctesting.TestChain{}
	consumerApps := []T{}
	for i := 0; i < numConsumers; i++ {
		chainID := ibctesting.GetChainID(i + 2)
		testChain := ibctesting.NewTestChainWithValSet(t, coordinator,
			appIniter, chainID, providerChain.Vals, providerChain.Signers)

		coordinator.Chains[chainID] = testChain
		consumerChains = append(consumerChains, testChain)
		consumerApps = append(consumerApps, testChain.App.(T))
	}

	return consumerChains, consumerApps
}
