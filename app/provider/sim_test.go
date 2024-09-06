package app_test

import (
	"fmt"
	"math/rand"
	"os"
	"testing"

	spew "github.com/davecgh/go-spew/spew"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/store"

	"github.com/cosmos/cosmos-sdk/baseapp"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/cosmos-sdk/server"
	simtestutil "github.com/cosmos/cosmos-sdk/testutil/sims"
	simtypes "github.com/cosmos/cosmos-sdk/types/simulation"
	"github.com/cosmos/cosmos-sdk/x/simulation"
	simcli "github.com/cosmos/cosmos-sdk/x/simulation/client/cli"

	providerapp "github.com/cosmos/interchain-security/v6/app/provider"
)

func init() {
	simcli.GetSimulatorFlags()
}

// interBlockCacheOpt returns a BaseApp option function that sets the persistent
// inter-block write-through cache.
func interBlockCacheOpt() func(*baseapp.BaseApp) {
	return baseapp.SetInterBlockCache(store.NewCommitKVStoreCacheManager())
}

// fauxMerkleModeOpt returns a BaseApp option to use a dbStoreAdapter instead of
// an IAVLStore for faster simulation speed.
func fauxMerkleModeOpt(bapp *baseapp.BaseApp) {
	bapp.SetFauxMerkleMode()
}

func TestFullAppSimulation(t *testing.T) {
	config := simcli.NewConfigFromFlags()
	config.ChainID = "provi"

	// if no seed is provided (aka we use the default seed), override this by choosing an actually random seed
	if config.Seed == simcli.DefaultSeedValue {
		fmt.Printf("Default seed value %v detected, using random seed value\n", simcli.DefaultSeedValue)
		config.Seed = int64(rand.Uint32())
	}

	fmt.Println("========================================")
	fmt.Println("Running with the configuration:")
	fmt.Println(spew.Sdump(config))
	fmt.Println("========================================")

	db, dir, logger, skip, err := simtestutil.SetupSimulation(config, "leveldb-app-sim", "Simulation", simcli.FlagVerboseValue, simcli.FlagEnabledValue)
	if skip {
		t.Skip("skipping application simulation")
	}
	require.NoError(t, err, "simulation setup failed")

	defer func() {
		require.NoError(t, db.Close())
		require.NoError(t, os.RemoveAll(dir))
	}()

	appOptions := make(simtestutil.AppOptionsMap, 0)
	appOptions[flags.FlagHome] = providerapp.DefaultNodeHome
	appOptions[server.FlagInvCheckPeriod] = simcli.FlagPeriodValue

	app := providerapp.New(logger, db, nil, true, appOptions, fauxMerkleModeOpt, interBlockCacheOpt(), baseapp.SetChainID("provi"))
	require.Equal(t, "interchain-security-p", app.Name())

	encoding := providerapp.MakeTestEncodingConfig()

	genesisState := providerapp.NewDefaultGenesisState(encoding.Codec)

	// run randomized simulation
	_, simParams, simErr := simulation.SimulateFromSeed(
		t,
		os.Stdout,
		app.BaseApp,
		simtestutil.AppStateFn(encoding.Codec, app.SimulationManager(), genesisState),
		simtypes.RandomAccounts, // Replace with own random account function if using keys other than secp256k1
		simtestutil.SimulationOperations(app, app.AppCodec(), config),
		providerapp.ComputeBankBlockedAddrs(app),
		config,
		app.AppCodec(),
	)

	// export state and simParams before the simulation error is checked
	err = simtestutil.CheckExportSimulation(app, config, simParams)
	require.NoError(t, err)
	require.NoError(t, simErr)

	if config.Commit {
		simtestutil.PrintStats(db)
	}
}
