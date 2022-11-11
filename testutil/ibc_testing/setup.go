package ibc_testing

// Contains util functions for using the IBC testing package with CCV.

import (
	"encoding/json"
	"testing"

	"github.com/cosmos/cosmos-sdk/simapp"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	"github.com/tendermint/spm/cosmoscmd"
	"github.com/tendermint/tendermint/libs/log"
	tmdb "github.com/tendermint/tm-db"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/app/provider"
)

var (
	provChainID = ibctesting.GetChainID(1)
)

// ProviderAppIniter implements ibctesting.AppIniter for a provider app
func ProviderAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := cosmoscmd.MakeEncodingConfig(appProvider.ModuleBasics)
	testApp := appProvider.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, appProvider.NewDefaultGenesisState(encoding.Marshaler)
}

// ConsumerAppIniter implements ibctesting.AppIniter for a consumer app
func ConsumerAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := cosmoscmd.MakeEncodingConfig(appConsumer.ModuleBasics)
	testApp := appConsumer.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, appConsumer.NewDefaultGenesisState(encoding.Marshaler)
}

// DemocracyConsumerAppIniter implements ibctesting.AppIniter for a democracy consumer app
func DemocracyConsumerAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := cosmoscmd.MakeEncodingConfig(appConsumerDemocracy.ModuleBasics)
	testApp := appConsumerDemocracy.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, appConsumerDemocracy.NewDefaultGenesisState(encoding.Marshaler)
}

// NewCoordinatorWithProvider initializes an IBC testing Coordinator with a properly setup provider
func NewCoordinatorWithProvider(t *testing.T) (*ibctesting.Coordinator, *ibctesting.TestChain) {
	coordinator := ibctesting.NewCoordinator(t, 0)
	provider := ibctesting.NewTestChain(t, coordinator, ProviderAppIniter, provChainID)
	coordinator.Chains[provChainID] = provider
	return coordinator, provider
}

func AddConsumersToCoordinator(coordinator *ibctesting.Coordinator,
	t *testing.T, numConsumers int, appIniter ibctesting.AppIniter) (consumers []*ibctesting.TestChain) {

	providerChain := coordinator.GetChain(provChainID)

	// Instantiate specified number of consumers, add them to the coordinator and returned slice
	for i := 0; i < numConsumers; i++ {
		chainID := ibctesting.GetChainID(i + 2)
		testChain := ibctesting.NewTestChainWithValSet(t, coordinator,
			appIniter, chainID, providerChain.Vals, providerChain.Signers)

		coordinator.Chains[chainID] = testChain
		consumers = append(consumers, testChain)
	}

	return consumers
}
