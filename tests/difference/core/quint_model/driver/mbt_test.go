package main

import (
	"fmt"
	"log"
	"reflect"
	"testing"
	"time"

	cmttypes "github.com/cometbft/cometbft/types"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"

	"github.com/informalsystems/itf-go/itf"
	"github.com/stretchr/testify/require"
)

const verbose = false

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

	// sanity check: each expected var name should be in the set
	for _, expectedVarName := range expectedVarNames {
		_, ok := varNames[expectedVarName]
		require.True(t, ok, "Expected var name %v not found in actual var names %v", expectedVarName, varNames)
	}
	// extra var names are ok, so no need to change the length

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

	// remember the time offsets to be able to compare times to the model
	// this is necessary because the system needs to do many steps to initialize the chains,
	// which is abstracted away in the model
	timeOffsets := make(map[ChainId]time.Time, len(chains))
	for _, chain := range chains {
		timeOffsets[ChainId(chain)] = driver.time(ChainId(chain))
	}

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
			continue
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

			// we need 2 blocks, because for a packet sent at height H, the receiving chain
			// needs a header of height H+1 to accept the packet
			// so we do one time advancement with a very small increment,
			// and then increment the rest of the time]

			// TODO: start and stop consumers
			driver.endAndBeginBlock("provider", 1)
			driver.endAndBeginBlock("provider", time.Duration(timeAdvancement)*time.Second-1)
		case "EndAndBeginBlockForConsumer":
			consumerChain := lastAction["consumerChain"].Value.(string)
			timeAdvancement := lastAction["timeAdvancement"].Value.(int64)
			t.Log("EndAndBeginBlockForConsumer", consumerChain, timeAdvancement)

			// as in EndAndBeginBlockForProvider, we need to produce 2 blocks,
			// while still honoring the time advancement
			driver.endAndBeginBlock(ChainId(consumerChain), 1)
			driver.endAndBeginBlock(ChainId(consumerChain), time.Duration(timeAdvancement)*time.Second-1)
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

		if verbose {
			t.Logf("Current actual state: %s", driver.getStateString())
		}

		currentModelState := state.VarValues["currentState"].Value.(itf.MapExprType)
		// check that the actual state is the same as the model state

		// check validator sets - provider current validator set should be the one from the staking keeper

		// provider
		// consumers - current validator set does not correspond to anything,
		// we can only check the head of the voting power history
		// no assignment found, so providerConsAddr is the consumerConsAddr
		t.Log("Comparing validator sets")
		CompareValidatorSets(t, driver, currentModelState, consumers, index)
		t.Log("Validator sets match")

		// check times - sanity check that the block times match the ones from the model
		t.Log("Comparing timestamps")
		CompareTimes(t, driver, consumers, currentModelState, timeOffsets)
		t.Log("Timestamps match")

		// check sent packets: we check that the package queues in the model and the system have the same length.
		t.Log("Comparing packet queues")
		for _, consumer := range consumers {
			ComparePacketQueues(t, driver, currentModelState, consumer)
		}
		t.Log("Packet queues match")
	}
	t.FailNow()
}

func CompareValidatorSets(t *testing.T, driver *Driver, currentModelState map[string]itf.Expr, consumers []string, index int) {
	modelValSet := ValidatorSet(currentModelState, "provider")
	curValSet := driver.providerValidatorSet("provider")

	actualValSet := make(map[string]int64, len(curValSet))

	for _, val := range curValSet {
		valName := val.Description.Moniker
		actualValSet[valName] = int64(val.Tokens.Int64())
	}

	require.NoError(t, CompareValSet(modelValSet, actualValSet), "Validator sets do not match")

	for _, consumer := range consumers {
		modelValSet = HistoricalValidatorSet(currentModelState, consumer, 0)

		consumerVals := driver.consumerValidatorSet(ChainId(consumer))
		consumerCurValSet := make(map[string]int64, len(consumerVals))
		for _, val := range consumerVals {
			pubkey, err := val.ConsPubKey()
			require.NoError(t, err, "Error getting pubkey")

			consAddr := providertypes.NewConsumerConsAddress(sdktypes.ConsAddress(pubkey.Address().Bytes()))

			providerConsAddr, found := driver.providerKeeper().GetValidatorByConsumerAddr(driver.providerCtx(), consumer, consAddr)
			if !found {
				providerConsAddr = providertypes.NewProviderConsAddress(consAddr.Address)
			}

			providerVal, found := driver.providerStakingKeeper().GetValidatorByConsAddr(driver.providerCtx(), providerConsAddr.Address)
			require.True(t, found, "Error getting provider validator")

			consumerCurValSet[providerVal.GetMoniker()] = int64(val.Power)
		}
		for val, power := range modelValSet {
			_ = val
			intPow := power.Value.(int64)
			_ = intPow
		}
		require.NoError(t, CompareValSet(modelValSet, consumerCurValSet), "Validator sets do not match for consumer %v", consumer)
	}
}

// ComparePacketQueues compares the packet queues in the model to the packet queues in the system.
// It compares both incoming (provider->consumer) and outgoing (consumer->provider) packets.
// It only takes the number of packets into account, not the contents.
func ComparePacketQueues(
	t *testing.T,
	driver *Driver,
	currentModelState map[string]itf.Expr,
	consumer string,
) {
	ComparePacketQueue(t, driver, currentModelState, Provider, consumer)
	ComparePacketQueue(t, driver, currentModelState, consumer, Provider)
}

func ComparePacketQueue(t *testing.T, driver *Driver, currentModelState map[string]itf.Expr, sender string, receiver string) {
	modelSenderQueue := PacketQueue(currentModelState, sender, receiver)
	actualSenderQueue := driver.packetQueue(ChainId(sender), ChainId(receiver))

	require.Equal(t,
		len(modelSenderQueue),
		len(actualSenderQueue),
		"Packet queues do not match for sender %v, receiver %v",
		sender,
		receiver)
}

// CompareTimes compares the block times in the model to the block times in the system.
// It takes into account the timeOffsets, which should be the starting times
// of the chains in the system after the system has been initialized.
func CompareTimes(
	t *testing.T,
	driver *Driver,
	consumers []string,
	currentModelState map[string]itf.Expr,
	timeOffsets map[ChainId]time.Time,
) {
	providerLastTimestamp := Time(currentModelState, "provider")
	actualProviderTime := driver.time("provider")
	providerOffset := timeOffsets["provider"]

	require.Equal(t,
		providerLastTimestamp,
		actualProviderTime.Unix()-providerOffset.Unix(),
		"Block times do not match")

	for _, chain := range consumers {
		modelLastTimestamp := Time(currentModelState, chain)
		actualChainTime := driver.time(ChainId(chain))

		require.Equal(t,
			modelLastTimestamp,
			actualChainTime.Unix()-timeOffsets[ChainId(chain)].Unix(),
			"Block times do not match")
	}
}

// CompareValSet compares the validator set in the model to the validator set in the system.
// The model validator set is given as a map from validator name to power,
// whereas the system validator set is given as a slice of validators.
// The names in the model validator set are expected to correspond to the monikers in the system validator set.
func CompareValSet(modelValSet map[string]itf.Expr, systemValSet map[string]int64) error {
	expectedValSet := make(map[string]int64, len(modelValSet))
	for val, power := range modelValSet {
		expectedValSet[val] = power.Value.(int64)
	}

	if !reflect.DeepEqual(expectedValSet, systemValSet) {
		return fmt.Errorf("Model validator set %v, system validator set %v", expectedValSet, systemValSet)
	}
	return nil
}
