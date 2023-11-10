package main

import (
	"log"
	"testing"
	"time"

	cmttypes "github.com/cometbft/cometbft/types"
	"github.com/cosmos/interchain-security/v3/testutil/integration"
	"github.com/informalsystems/itf-go/itf"
	"github.com/stretchr/testify/require"
)

// Given a map from node names to voting powers, create a validator set with the right voting powers.
// All nodes should be included in the voting power map, even if they have voting power 0.
// This way, the nodes will have validators (that can later be assigned voting powers) and signers created for them.
//
// Returns:
// - a validator set
// - a map from node names to validator objects and
// - a map from validator addresses to private validators (signers)
func CreateValSet(t *testing.T, initialValidatorSet map[string]int64) (*cmttypes.ValidatorSet, map[string]*cmttypes.Validator, map[string]cmttypes.PrivValidator) {
	// create a valSet and signers, but the voting powers will not yet be right
	valSet, _, signers := integration.CreateValidators(t, len(initialValidatorSet))

	// create a map from validator names to validators
	valMap := make(map[string]*cmttypes.Validator)

	// impose an order on the validators
	valNames := make([]string, 0, len(initialValidatorSet))
	for valName := range initialValidatorSet {
		valNames = append(valNames, valName)
	}

	// assign the validators from the created valSet to valNames in the chosen order
	for i, valName := range valNames {
		_, val := valSet.GetByIndex(int32(i))
		valMap[valName] = val
	}

	// create a valSet that has the right voting powers
	vals := make([]*cmttypes.Validator, len(valNames))
	for index, valName := range valNames {
		_, val := valSet.GetByIndex(int32(index))
		val.VotingPower = initialValidatorSet[valName]
		vals[index] = val
	}

	// override the valSet by creating a new one with the right voting powers
	valSet = cmttypes.NewValidatorSet(vals)
	return valSet, valMap, signers
}

func TestItfTrace(t *testing.T) {
	path := "trace.json"
	t.Logf("🟡 Testing trace %s", path)

	// Load trace
	trace := &itf.Trace{}
	if err := trace.LoadFromFile(path); err != nil {
		log.Fatalf("Error loading trace file: %s", err)
	}

	expectedVarNames := []string{"currentState", "params", "trace"}

	varNames := make(map[string]bool, len(expectedVarNames))
	// populate the set
	for _, varName := range trace.Vars {
		varNames[varName] = true
	}

	// sanity check: there are as many var names as we expect
	require.Equal(t, len(expectedVarNames), len(varNames), "Expected %v var names, got %v", expectedVarNames, varNames)

	// sanity check: each expected var name should be in the set
	for _, expectedVarName := range expectedVarNames {
		_, ok := varNames[expectedVarName]
		require.True(t, ok, "Expected var name %v not found in actual var names %v", expectedVarName, varNames)
	}

	t.Log("Reading params...")
	params := trace.States[0].VarValues["params"].Value.(itf.MapExprType)

	consumersExpr := params["ConsumerChains"].Value.(itf.ListExprType)
	initialValSetExpr := params["InitialValidatorSet"].Value.(itf.MapExprType)

	initialValSet := make(map[string]int64)
	for val, power := range initialValSetExpr {
		initialValSet[val] = power.Value.(int64)
	}

	consumers := make([]string, len(consumersExpr))
	for i, chain := range consumersExpr {
		consumers[i] = chain.Value.(string)
	}

	chains := append(consumers, "provider")

	t.Log("Chains are: ", chains)

	// create params struct
	vscTimeout := time.Duration(params["VscTimeout"].Value.(int64))

	unbondingPeriodPerChain := make(map[ChainId]time.Duration, len(consumers))
	trustingPeriodPerChain := make(map[ChainId]time.Duration, len(consumers))
	ccvTimeoutPerChain := make(map[ChainId]time.Duration, len(consumers))
	for _, consumer := range chains {
		unbondingPeriodPerChain[ChainId(consumer)] = time.Duration(params["UnbondingPeriodPerChain"].Value.(itf.MapExprType)[consumer].Value.(int64)) * time.Second
		trustingPeriodPerChain[ChainId(consumer)] = time.Duration(params["TrustingPeriodPerChain"].Value.(itf.MapExprType)[consumer].Value.(int64)) * time.Second
		ccvTimeoutPerChain[ChainId(consumer)] = time.Duration(params["CcvTimeout"].Value.(itf.MapExprType)[consumer].Value.(int64)) * time.Second
	}

	modelParams := ModelParams{
		VscTimeout:              vscTimeout,
		CcvTimeout:              ccvTimeoutPerChain,
		UnbondingPeriodPerChain: unbondingPeriodPerChain,
		TrustingPeriodPerChain:  trustingPeriodPerChain,
	}

	valExprs := params["Nodes"].Value.(itf.ListExprType)
	valNames := make([]string, len(valExprs))
	for i, val := range valExprs {
		valNames[i] = val.Value.(string)
	}

	// dummyValSet is a valSet with the right validators, but not yet right powers
	valSet, addressMap, signers := CreateValSet(t, initialValSet)

	// get a slice of validators in the right order
	nodes := make([]*cmttypes.Validator, len(valNames))
	for i, valName := range valNames {
		nodes[i] = addressMap[valName]
	}

	driver := newDriver(t, nodes, valNames)
	driver.setupChains(modelParams, valSet, signers, nodes, valNames, consumers)

	t.Log("Started chains")

	t.Log("Reading the trace...")

	for index, state := range trace.States {
		t.Logf("Reading state %v", index)

		// modelState := state.VarValues["currentState"]
		trace := state.VarValues["trace"].Value.(itf.ListExprType)
		// fmt.Println(modelState)
		lastAction := trace[len(trace)-1].Value.(itf.MapExprType)

		actionKind := lastAction["kind"].Value.(string)
		switch actionKind {
		case "init":
			t.Log("Initializing...")
		case "VotingPowerChange":
			node := lastAction["validator"].Value.(string)
			changeAmount := lastAction["changeAmount"].Value.(int64)
			t.Logf("Changing provider voting power of %v by %v", node, changeAmount)

			valIndex := getIndexOfString(node, valNames)

			if changeAmount > 0 {
				// delegate to the validator
				driver.delegate(int64(valIndex), changeAmount)
			} else {
				// undelegate from the validator
				driver.undelegate(int64(valIndex), -changeAmount)
			}
		case "EndAndBeginBlockForProvider":
			timeAdvancement := lastAction["timeAdvancement"].Value.(int64)
			consumersToStart := lastAction["consumersToStart"].Value.(itf.ListExprType)
			consumersToStop := lastAction["consumersToStop"].Value.(itf.ListExprType)
			t.Log("EndAndBeginBlockForProvider", timeAdvancement, consumersToStart, consumersToStop)

			// TODO continue here
			totalDuration := time.Duration(timeAdvancement) * time.Second
			halfDuration := totalDuration / 2
			halfDuration = halfDuration.Round(time.Second)
			remainingDuration := totalDuration - halfDuration
			remainingDuration = remainingDuration.Round(time.Second)

			require.True(t, halfDuration+remainingDuration == totalDuration)

			// TODO: start and stop consumers
			driver.endAndBeginBlock("provider", time.Duration(1)*time.Second) //, func() {})
			driver.endAndBeginBlock("provider", time.Duration(1)*time.Second) //, func() {})
			driver.endAndBeginBlock("provider", time.Duration(1)*time.Second) //, func() {})
		case "EndAndBeginBlockForConsumer":
			consumerChain := lastAction["consumerChain"].Value.(string)
			timeAdvancement := lastAction["timeAdvancement"].Value.(int64)
			t.Log("EndAndBeginBlockForConsumer", consumerChain, timeAdvancement)

			// TODO continue here
			totalDuration := time.Duration(timeAdvancement) * time.Second
			halfDuration := totalDuration / 2
			halfDuration = halfDuration.Round(time.Second)
			remainingDuration := totalDuration - halfDuration
			remainingDuration = remainingDuration.Round(time.Second)
			// this is trying to split into two parts, but fails because all need to be non-0
			// updating client multiple times with headers that do not progress in time is not allowed

			require.True(t, halfDuration+remainingDuration == totalDuration)

			// time duration needs 3 parts because the packet needs 3 commits to be delivered
			driver.endAndBeginBlock(ChainId(consumerChain), time.Duration(1)*time.Second) //, func() {})
			driver.endAndBeginBlock(ChainId(consumerChain), time.Duration(1)*time.Second) //, func() {})
			driver.endAndBeginBlock(ChainId(consumerChain), time.Duration(1)*time.Second) //, func() {})
		case "DeliverVscPacket":
			consumerChain := lastAction["consumerChain"].Value.(string)
			t.Log("DeliverVscPacket", consumerChain)

			driver.DeliverPacketToConsumer(ChainId(consumerChain))
		case "DeliverVscMaturedPacket":
			consumerChain := lastAction["consumerChain"].Value.(string)
			t.Log("DeliverVscMaturedPacket", consumerChain)

			driver.DeliverPacketFromConsumer(ChainId(consumerChain))
		default:

			log.Fatalf("Error loading trace file %s, step %v: do not know action type %s",
				path, index, actionKind)
		}

		t.Logf("Current actual state: %s", driver.getStateString())
	}
	t.FailNow()
}
