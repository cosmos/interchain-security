package ibc_testing

// Contains example setup code for running integration tests against a provider, consumer,
// and/or democracy consumer app.go implementation. This file is meant to be pattern matched
// for apps running integration tests against their implementation.

import (
	"encoding/json"

	db "github.com/cosmos/cosmos-db"
	ibctesting "github.com/cosmos/ibc-go/v8/testing"

	simtestutil "github.com/cosmos/cosmos-sdk/testutil/sims"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"cosmossdk.io/log"
	"github.com/cometbft/cometbft/abci/types"

	appConsumer "github.com/cosmos/interchain-security/v5/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/v5/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/v5/app/provider"
	consumertypes "github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

var (
	_ AppIniter       = ProviderAppIniter
	_ ValSetAppIniter = ConsumerAppIniter
	_ ValSetAppIniter = DemocracyConsumerAppIniter
)

// ProviderAppIniter implements ibctesting.AppIniter for a provider app
func ProviderAppIniter() (ibctesting.TestingApp, map[string]json.RawMessage) {
	encoding := appProvider.MakeTestEncodingConfig()
	testApp := appProvider.New(log.NewNopLogger(), db.NewMemDB(), nil, true, simtestutil.EmptyAppOptions{})
	return testApp, appProvider.NewDefaultGenesisState(encoding.Codec)
}

// ConsumerAppIniter returns a ibctesting.ValSetAppIniter for a consumer app
func ConsumerAppIniter(initValPowers []types.ValidatorUpdate) AppIniter {
	return func() (ibctesting.TestingApp, map[string]json.RawMessage) {
		encoding := appConsumer.MakeTestEncodingConfig()
		testApp := appConsumer.New(log.NewNopLogger(), db.NewMemDB(), nil, true, simtestutil.EmptyAppOptions{})
		genesisState := appConsumer.NewDefaultGenesisState(encoding.Codec)
		// NOTE: starting from ibc-go/v7/testing.SetupWithGenesisValSet requires a staking module
		// genesisState or it panics. Feed a minimum one.
		genesisState[stakingtypes.ModuleName] = encoding.Codec.MustMarshalJSON(
			&stakingtypes.GenesisState{
				Params: stakingtypes.Params{BondDenom: sdk.DefaultBondDenom},
			},
		)
		// Feed consumer genesis with provider validators
		var consumerGenesis ccvtypes.ConsumerGenesisState
		encoding.Codec.MustUnmarshalJSON(genesisState[consumertypes.ModuleName], &consumerGenesis)
		consumerGenesis.Provider.InitialValSet = initValPowers
		consumerGenesis.Params.Enabled = true
		genesisState[consumertypes.ModuleName] = encoding.Codec.MustMarshalJSON(&consumerGenesis)

		return testApp, genesisState
	}
}

// DemocracyConsumerAppIniter implements ibctesting.ValSetAppIniter for a democracy consumer app
func DemocracyConsumerAppIniter(initValPowers []types.ValidatorUpdate) AppIniter {
	return func() (ibctesting.TestingApp, map[string]json.RawMessage) {
		encoding := appConsumerDemocracy.MakeTestEncodingConfig()
		testApp := appConsumerDemocracy.New(log.NewNopLogger(), db.NewMemDB(), nil, true, simtestutil.EmptyAppOptions{})
		genesisState := appConsumerDemocracy.NewDefaultGenesisState(encoding.Codec)
		// Feed consumer genesis with provider validators
		// TODO See if useful for democracy
		var consumerGenesis ccvtypes.ConsumerGenesisState
		encoding.Codec.MustUnmarshalJSON(genesisState[consumertypes.ModuleName], &consumerGenesis)
		consumerGenesis.Provider.InitialValSet = initValPowers
		consumerGenesis.Params.Enabled = true
		genesisState[consumertypes.ModuleName] = encoding.Codec.MustMarshalJSON(&consumerGenesis)

		return testApp, genesisState
	}
}
