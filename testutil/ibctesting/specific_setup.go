package ibctesting

// Contains example setup code for running e2e tests against a provider, consumer,
// and/or democracy consumer app.go implementation. This file is meant to be pattern matched
// for apps running e2e tests against their implementation.

import (
	"encoding/json"

	ibctesting "github.com/cosmos/interchain-security/v2/legacy_ibc_testing/testing"

	tmdb "github.com/cometbft/cometbft-db"
	"github.com/cometbft/cometbft/libs/log"

	simtestutil "github.com/cosmos/cosmos-sdk/testutil/sims"
	appConsumer "github.com/cosmos/interchain-security/v2/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/v2/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/v2/app/provider"
)

// ProviderAppIniter implements ibctesting.AppIniter for a provider app
func ProviderAppIniter() (ibctesting.AppTest, map[string]json.RawMessage) {
	encoding := appProvider.MakeEncodingConfigProviderApp()
	testApp := appProvider.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true,
		simtestutil.EmptyAppOptions{})
	return testApp, appProvider.NewDefaultGenesisState(encoding.Codec)
}

// ConsumerAppIniter implements ibctesting.AppIniter for a consumer app
func ConsumerAppIniter() (ibctesting.AppTest, map[string]json.RawMessage) {
	encoding := appConsumer.MakeEncodingConfigDemocracyConsumerApp()
	testApp := appConsumer.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true,
		simtestutil.EmptyAppOptions{})
	return testApp, appConsumer.NewDefaultGenesisState(encoding.Codec)
}

// DemocracyConsumerAppIniter implements ibctesting.AppIniter for a democracy consumer app
func DemocracyConsumerAppIniter() (ibctesting.AppTest, map[string]json.RawMessage) {
	encoding := appConsumerDemocracy.MakeEncodingConfigDemocracyConsumerApp()
	testApp := appConsumerDemocracy.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true,
		simtestutil.EmptyAppOptions{})
	return testApp, appConsumerDemocracy.NewDefaultGenesisState(encoding.Codec)
}
