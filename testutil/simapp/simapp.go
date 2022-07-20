package simapp

import (
	"encoding/json"
	"testing"

	"github.com/cosmos/cosmos-sdk/simapp"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appWasm "github.com/CosmWasm/wasmd/app"
	"github.com/CosmWasm/wasmd/x/wasm"
	wasmKeeper "github.com/CosmWasm/wasmd/x/wasm/keeper"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/tendermint/spm/cosmoscmd"
	"github.com/tendermint/tendermint/libs/log"
	tmdb "github.com/tendermint/tm-db"
)

var chainTypeToIniter = map[ConsumerChainType]func() (ibctesting.TestingApp, map[string]json.RawMessage){
	Minimal:  SetupTestingAppConsumer,
	CosmWasm: SetupCosmWasmAppConsumer,
}

func SetupTestingappProvider() (ibctesting.TestingApp, map[string]json.RawMessage) {
	db := tmdb.NewMemDB()
	// encCdc := app.MakeTestEncodingConfig()
	encoding := cosmoscmd.MakeEncodingConfig(appProvider.ModuleBasics)
	testApp := appProvider.New(log.NewNopLogger(), db, nil, true, map[int64]bool{}, simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, appProvider.NewDefaultGenesisState(encoding.Marshaler)
}

func SetupTestingAppConsumer() (ibctesting.TestingApp, map[string]json.RawMessage) {
	db := tmdb.NewMemDB()
	// encCdc := app.MakeTestEncodingConfig()
	encoding := cosmoscmd.MakeEncodingConfig(appConsumer.ModuleBasics)
	testApp := appConsumer.New(log.NewNopLogger(), db, nil, true, map[int64]bool{}, simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, appConsumer.NewDefaultGenesisState(encoding.Marshaler)
}

func SetupCosmWasmAppConsumer() (ibctesting.TestingApp, map[string]json.RawMessage) {
	db := tmdb.NewMemDB()
	testApp := appWasm.NewWasmApp(log.NewNopLogger(), db, nil, true, map[int64]bool{}, simapp.DefaultNodeHome, 5, appWasm.MakeEncodingConfig(), wasm.DisableAllProposals, appWasm.EmptyBaseAppOptions{}, []wasmKeeper.Option{})

	return testApp, appWasm.NewDefaultGenesisState()
}

// NewCoordinator initializes Coordinator with 0 TestChains
func NewBasicCoordinator(t *testing.T) *ibctesting.Coordinator {
	chains := make(map[string]*ibctesting.TestChain)
	coord := &ibctesting.Coordinator{
		T:           t,
		CurrentTime: ibctesting.GlobalStartTime,
	}
	coord.Chains = chains
	return coord
}

func NewProviderConsumerCoordinator(t *testing.T, chainType ConsumerChainType) (*ibctesting.Coordinator, *ibctesting.TestChain, *ibctesting.TestChain) {
	coordinator := NewBasicCoordinator(t)
	chainID := ibctesting.GetChainID(1)
	coordinator.Chains[chainID] = ibctesting.NewTestChain(t, coordinator, SetupTestingappProvider, chainID)
	providerChain := coordinator.GetChain(chainID)
	chainID = ibctesting.GetChainID(2)
	coordinator.Chains[chainID] = ibctesting.NewTestChainWithValSet(t, coordinator,
		chainTypeToIniter[chainType], chainID, providerChain.Vals, providerChain.Signers)
	consumerChain := coordinator.GetChain(chainID)
	return coordinator, providerChain, consumerChain
}
