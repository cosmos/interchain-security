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

	"github.com/cosmos/interchain-security/app"
)

// New creates application instance with in-memory database and disabled logging.
func New(dir string) cosmoscmd.App {
	db := tmdb.NewMemDB()
	logger := log.NewNopLogger()

	encoding := cosmoscmd.MakeEncodingConfig(app.ModuleBasics)

	a := app.New(logger, db, nil, true, map[int64]bool{}, dir, 0, encoding,
		simapp.EmptyAppOptions{})
	// InitChain updates deliverState which is required when app.NewContext is called
	a.InitChain(abci.RequestInitChain{
		ConsensusParams: defaultConsensusParams,
		AppStateBytes:   []byte("{}"),
	})
	return a
}

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

func SetupTestingParentApp() (ibctesting.TestingApp, map[string]json.RawMessage) {
	db := tmdb.NewMemDB()
	// encCdc := app.MakeTestEncodingConfig()
	encoding := cosmoscmd.MakeEncodingConfig(app.ModuleBasics)
	testApp := app.New(log.NewNopLogger(), db, nil, true, map[int64]bool{}, simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, app.NewDefaultGenesisState(encoding.Marshaler)
}

func SetupTestingChildApp() (ibctesting.TestingApp, map[string]json.RawMessage) {
	db := tmdb.NewMemDB()
	// encCdc := app.MakeTestEncodingConfig()
	encoding := cosmoscmd.MakeEncodingConfig(app.ModuleBasics)
	testApp := app.New(log.NewNopLogger(), db, nil, true, map[int64]bool{}, simapp.DefaultNodeHome, 5, encoding, simapp.EmptyAppOptions{}).(ibctesting.TestingApp)
	return testApp, app.NewDefaultGenesisState(encoding.Marshaler)
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
func NewParentChildCoordinator(t *testing.T) (*ibctesting.Coordinator, *ibctesting.TestChain, *ibctesting.TestChain) {
	coordinator := NewBasicCoordinator(t)
	chainID := ibctesting.GetChainID(0)
	coordinator.Chains[chainID] = ibctesting.NewTestChain(t, coordinator, SetupTestingParentApp, chainID)
	parentChain := coordinator.GetChain(chainID)
	chainID = ibctesting.GetChainID(1)
	coordinator.Chains[chainID] = ibctesting.NewTestChainWithValSet(t, coordinator,
		SetupTestingChildApp, chainID, parentChain.Vals, parentChain.Signers)
	childChain := coordinator.GetChain(chainID)
	return coordinator, parentChain, childChain
}
