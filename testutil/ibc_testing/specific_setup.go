package ibc_testing

// Contains example setup code for running integration tests against a provider, consumer,
// and/or democracy consumer app.go implementation. This file is meant to be pattern matched
// for apps running integration tests against their implementation.

import (
	"encoding/json"

	simtestutil "github.com/cosmos/cosmos-sdk/testutil/sims"

	tmdb "github.com/cometbft/cometbft-db"
	"github.com/cometbft/cometbft/libs/log"

	appConsumer "github.com/cosmos/interchain-security/v3/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/v3/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/v3/app/provider"
	ibctesting "github.com/cosmos/interchain-security/v3/legacy_ibc_testing/testing"
)

// ProviderAppIniter implements ibctesting.AppIniter for a provider app
func ProviderAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := appProvider.MakeTestEncodingConfig()
	testApp := appProvider.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, simtestutil.EmptyAppOptions{})
	return testApp, appProvider.NewDefaultGenesisState(encoding.Codec)
}

<<<<<<< HEAD
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
=======
// ConsumerAppIniter returns a ibctesting.ValSetAppIniter for a consumer app
func ConsumerAppIniter(initValPowers []types.ValidatorUpdate) AppIniter {
	return func() (ibctesting.TestingApp, map[string]json.RawMessage) {
		encoding := appConsumer.MakeTestEncodingConfig()
		testApp := appConsumer.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, simtestutil.EmptyAppOptions{})
		genesisState := appConsumer.NewDefaultGenesisState(encoding.Codec)
		// NOTE ibc-go/v7/testing.SetupWithGenesisValSet requires a staking module
		// genesisState or it panics. Feed a minimum one.
		genesisState[stakingtypes.ModuleName] = encoding.Codec.MustMarshalJSON(
			&stakingtypes.GenesisState{
				Params: stakingtypes.Params{BondDenom: sdk.DefaultBondDenom},
			},
		)
		// Feed consumer genesis with provider validators
		var consumerGenesis ccvtypes.ConsumerGenesisState
		encoding.Codec.MustUnmarshalJSON(genesisState[consumertypes.ModuleName], &consumerGenesis)
		consumerGenesis.InitialValSet = initValPowers
		consumerGenesis.Params.Enabled = true
		genesisState[consumertypes.ModuleName] = encoding.Codec.MustMarshalJSON(&consumerGenesis)

		return testApp, genesisState
	}
}

// DemocracyConsumerAppIniter implements ibctesting.ValSetAppIniter for a democracy consumer app
func DemocracyConsumerAppIniter(initValPowers []types.ValidatorUpdate) AppIniter {
	return func() (ibctesting.TestingApp, map[string]json.RawMessage) {
		encoding := appConsumerDemocracy.MakeTestEncodingConfig()
		testApp := appConsumerDemocracy.New(log.NewNopLogger(), tmdb.NewMemDB(), nil, true, simtestutil.EmptyAppOptions{})
		genesisState := appConsumerDemocracy.NewDefaultGenesisState(encoding.Codec)
		// Feed consumer genesis with provider validators
		// TODO See if useful for democracy
		var consumerGenesis ccvtypes.ConsumerGenesisState
		encoding.Codec.MustUnmarshalJSON(genesisState[consumertypes.ModuleName], &consumerGenesis)
		consumerGenesis.InitialValSet = initValPowers
		consumerGenesis.Params.Enabled = true
		genesisState[consumertypes.ModuleName] = encoding.Codec.MustMarshalJSON(&consumerGenesis)

		return testApp, genesisState
	}
>>>>>>> df12b7e (refactor: Vaguely named consumer structs (#1288))
}
