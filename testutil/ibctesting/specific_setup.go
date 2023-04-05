package ibctesting

// Contains example setup code for running integration tests against a provider, consumer,
// and/or democracy consumer app.go implementation. This file is meant to be pattern matched
// for apps running integration tests against their implementation.

import (
	"encoding/json"

	"cosmossdk.io/simapp"

	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"

	tmdb "github.com/cometbft/cometbft-db"
	"github.com/cometbft/cometbft/libs/log"

	simtestutil "github.com/cosmos/cosmos-sdk/testutil/sims"
	"github.com/cosmos/interchain-security/app"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/app/provider"
)

// ProviderAppIniter implements ibctesting.AppIniter for a provider app
func ProviderAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := app.MakeEncodingConfigProviderApp()
	testApp := appProvider.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simtestutil.EmptyAppOptions{})
	return testApp, appProvider.NewDefaultGenesisState(encoding.Codec)
}

// ConsumerAppIniter implements ibctesting.AppIniter for a consumer app
func ConsumerAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := app.MakeEncodingConfigDemocracyConsumerApp()
	testApp := appConsumer.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simtestutil.EmptyAppOptions{})
	return testApp, appConsumer.NewDefaultGenesisState(encoding.Codec)
}

// DemocracyConsumerAppIniter implements ibctesting.AppIniter for a democracy consumer app
func DemocracyConsumerAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := app.MakeEncodingConfigDemocracyConsumerApp()
	testApp := appConsumerDemocracy.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simtestutil.EmptyAppOptions{})
	return testApp, appConsumerDemocracy.NewDefaultGenesisState(encoding.Codec)
}
