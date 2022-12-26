package ibc_testing

// Contains example setup code for running e2e tests against a provider, consumer,
// and/or democracy consumer app.go implementation. This file is meant to be pattern matched
// for apps running e2e tests against their implementation.

import (
	"encoding/json"

	"github.com/cosmos/cosmos-sdk/simapp"

	ibctesting "github.com/cosmos/interchain-security/ibc/testing"

	"github.com/tendermint/spm/cosmoscmd"
	"github.com/tendermint/tendermint/libs/log"
	tmdb "github.com/tendermint/tm-db"

	// TODO: Add back gaia ref
	//gaiaApp "github.com/cosmos/gaia/v8/app"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/app/provider"
)

// ProviderAppIniter implements ibctesting.AppIniter for a provider app
func ProviderAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := cosmoscmd.MakeEncodingConfig(appProvider.ModuleBasics)
	testApp := appProvider.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
		simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, appProvider.NewDefaultGenesisState(encoding.Marshaler)
}

// TODO: Fix Gaia version
//// GaiaAppIniter implements ibctesting.AppIniter for the gaia app
//func GaiaAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
//	encoding := gaiaApp.MakeTestEncodingConfig()
//	app := gaiaApp.NewGaiaApp(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, map[int64]bool{},
//		simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{})
//	testApp := ibctesting.TestingApp(app)
//	return testApp, gaiaApp.NewDefaultGenesisState()
//}

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
