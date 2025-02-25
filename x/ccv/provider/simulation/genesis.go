package simulation

import (
	"encoding/json"
	"fmt"
	"math/rand"

	"github.com/cosmos/cosmos-sdk/types/module"

	"github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
)

// Simulation parameter constants
const (
	// only includes params that make sense even with a single
	maxProviderConsensusValidators = "max_provider_consensus_validators"
)

// genMaxProviderConsensusValidators returns randomized maxProviderConsensusValidators
func genMaxProviderConsensusValidators(r *rand.Rand) int64 {
	return int64(r.Intn(250) + 1)
}

// RandomizedGenState generates a random GenesisState for staking
func RandomizedGenState(simState *module.SimulationState) {
	// params
	var (
		maxProviderConsensusVals int64
	)

	simState.AppParams.GetOrGenerate(maxProviderConsensusValidators, &maxProviderConsensusVals, simState.Rand, func(r *rand.Rand) { maxProviderConsensusVals = genMaxProviderConsensusValidators(r) })

	providerParams := types.DefaultParams()
	providerParams.MaxProviderConsensusValidators = maxProviderConsensusVals

	providerGenesis := types.DefaultGenesisState()
	providerGenesis.Params = providerParams

	bz, err := json.MarshalIndent(&providerGenesis.Params, "", " ")
	if err != nil {
		panic(err)
	}
	fmt.Printf("Selected randomly generated provider parameters:\n%s\n", bz)
	simState.GenState[types.ModuleName] = simState.Cdc.MustMarshalJSON(providerGenesis)
}
