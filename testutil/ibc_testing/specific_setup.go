package ibc_testing

// Contains example setup code for running integration tests against a provider, consumer,
// and/or democracy consumer app.go implementation. This file is meant to be pattern matched
// for apps running integration tests against their implementation.

import (
	"encoding/json"

	simtestutil "github.com/cosmos/cosmos-sdk/testutil/sims"
	ibctesting "github.com/cosmos/interchain-security/v3/legacy_ibc_testing/testing"

	tmdb "github.com/cometbft/cometbft-db"
	"github.com/cometbft/cometbft/libs/log"

	appConsumer "github.com/cosmos/interchain-security/v3/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/v3/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/v3/app/provider"
)

// ProviderAppIniter implements ibctesting.AppIniter for a provider app
func ProviderAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := appProvider.MakeTestEncodingConfig()
	testApp := appProvider.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, simtestutil.EmptyAppOptions{})
	return testApp, appProvider.NewDefaultGenesisState(encoding.Codec)
}

// ConsumerAppIniter implements ibctesting.AppIniter for a consumer app
func ConsumerAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := appConsumer.MakeTestEncodingConfig()
	testApp := appConsumer.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, simtestutil.EmptyAppOptions{})
	return testApp, appConsumer.NewDefaultGenesisState(encoding.Codec)
}

// DemocracyConsumerAppIniter implements ibctesting.AppIniter for a democracy consumer app
func DemocracyConsumerAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := appConsumerDemocracy.MakeTestEncodingConfig()
	testApp := appConsumerDemocracy.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, simtestutil.EmptyAppOptions{})
	return testApp, appConsumerDemocracy.NewDefaultGenesisState(encoding.Codec)
}
