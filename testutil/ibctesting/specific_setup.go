package ibctesting

// Contains example setup code for running e2e tests against a provider, consumer,
// and/or democracy consumer app.go implementation. This file is meant to be pattern matched
// for apps running e2e tests against their implementation.

import (
	"encoding/json"

	"github.com/cosmos/cosmos-sdk/simapp"

	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"

	"github.com/tendermint/spm/cosmoscmd"
	"github.com/tendermint/tendermint/libs/log"
	tmdb "github.com/tendermint/tm-db"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/app/provider"
)

// ProviderAppIniter implements ibctesting.AppIniter for a provider app
func ProviderAppIniter() (ibctesting.AppTest, map[string]json.RawMessage) {
	encoding := cosmoscmd.MakeEncodingConfig(appProvider.ModuleBasics)
	testApp := appProvider.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.AppTest)
	return testApp, appProvider.NewDefaultGenesisState(encoding.Marshaler)
}

// ConsumerAppIniter implements ibctesting.AppIniter for a consumer app
func ConsumerAppIniter() (ibctesting.AppTest, map[string]json.RawMessage) {
	encoding := cosmoscmd.MakeEncodingConfig(appConsumer.ModuleBasics)
	testApp := appConsumer.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.AppTest)
	return testApp, appConsumer.NewDefaultGenesisState(encoding.Marshaler)
}

// DemocracyConsumerAppIniter implements ibctesting.AppIniter for a democracy consumer app
func DemocracyConsumerAppIniter() (ibctesting.AppTest, map[string]json.RawMessage) {
	encoding := cosmoscmd.MakeEncodingConfig(appConsumerDemocracy.ModuleBasics)
	testApp := appConsumerDemocracy.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.AppTest)
	return testApp, appConsumerDemocracy.NewDefaultGenesisState(encoding.Marshaler)
}
