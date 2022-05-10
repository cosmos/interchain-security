package simapp

import (
	"encoding/json"
	"testing"
	"time"

	"github.com/cosmos/cosmos-sdk/simapp"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	"github.com/tendermint/spm/cosmoscmd"
	abci "github.com/tendermint/tendermint/abci/types"
	"github.com/tendermint/tendermint/libs/log"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
	tmdb "github.com/tendermint/tm-db"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
)

var defaultConsensusParams = &abci.ConsensusParams{
	Block: &abci.BlockParams{
		MaxBytes: 200000,
		MaxGas:   2000000,
	},
	Evidence: &tmproto.EvidenceParams{
		MaxAgeNumBlocks: 302400,
		MaxAgeDuration:  504 * time.Hour, // 3 weeks is the max duration
		MaxBytes:        10000,
	},
	Validator: &tmproto.ValidatorParams{
		PubKeyTypes: []string{
			tmtypes.ABCIPubKeyTypeEd25519,
		},
	},
}

func SetupTestingappProvider() (ibctesting.TestingApp, map[string]json.RawMessage) {
	db := tmdb.NewMemDB()
	// encCdc := app.MakeTestEncodingConfig()
	encoding := cosmoscmd.MakeEncodingConfig(appProvider.ModuleBasics)
	testApp := appProvider.New(log.NewNopLogger(), db, nil, true, map[int64]bool{}, simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, appProvider.NewDefaultGenesisState(encoding.Marshaler)
}

func SetupTestingappConsumer() (ibctesting.TestingApp, map[string]json.RawMessage) {
	db := tmdb.NewMemDB()
	// encCdc := app.MakeTestEncodingConfig()
	encoding := cosmoscmd.MakeEncodingConfig(appConsumer.ModuleBasics)
	testApp := appConsumer.New(log.NewNopLogger(), db, nil, true, map[int64]bool{}, simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, appConsumer.NewDefaultGenesisState(encoding.Marshaler)
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

// NewCoordinator initializes Coordinator with 0 TestChains
func NewProviderConsumerCoordinator(t *testing.T) (*ibctesting.Coordinator, *ibctesting.TestChain, *ibctesting.TestChain) {
	coordinator := NewBasicCoordinator(t)
	chainID := ibctesting.GetChainID(0)
	coordinator.Chains[chainID] = ibctesting.NewTestChain(t, coordinator, SetupTestingappProvider, chainID)
	providerChain := coordinator.GetChain(chainID)
	chainID = ibctesting.GetChainID(1)
	coordinator.Chains[chainID] = ibctesting.NewTestChainWithValSet(t, coordinator,
		SetupTestingappConsumer, chainID, providerChain.Vals, providerChain.Signers)
	consumerChain := coordinator.GetChain(chainID)
	return coordinator, providerChain, consumerChain
}
