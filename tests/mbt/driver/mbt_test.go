package main

import (
	"fmt"
	"log"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"testing"
	"time"

	ibctesting "github.com/cosmos/ibc-go/v7/testing"
	"github.com/informalsystems/itf-go/itf"
	"github.com/kylelemons/godebug/pretty"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"

	tmencoding "github.com/cometbft/cometbft/crypto/encoding"
	cmttypes "github.com/cometbft/cometbft/types"

	"github.com/cosmos/interchain-security/v4/testutil/integration"
	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/types"
)

const verbose = false

const TIMEDOUT_STATUS = "timedout"

// keep some interesting statistics
var stats = Stats{}

func TestMBT(t *testing.T) {
	dir := "traces"

	numTraces := 0

	ibctesting.TimeIncrement = 1 * time.Nanosecond

	err := filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if info.IsDir() {
			return nil
		}

		ext := filepath.Ext(path)
		if ext == ".json" || ext == ".itf" {
			fmt.Println("Running trace:", path)
			numTraces++
			RunItfTrace(t, path)
		}

		return nil
	})
	if err != nil {
		t.Fatal("Error:", err)
	}

	t.Log("✅ Running traces from the traces folder done")
	t.Log(numTraces, "traces run")

	// print some stats
	t.Logf("Highest observed voting power: %v", stats.highestObservedValPower)
	t.Logf("Number of started chains: %v", stats.numStartedChains)
	t.Logf("Number of stopped chains: %v", stats.numStops)
	t.Logf("Number of timeouts: %v", stats.numTimeouts)
	t.Logf("Number of sent packets: %v", stats.numSentPackets)
	t.Logf("Number of blocks: %v", stats.numBlocks)
	t.Logf("Number of transactions: %v", stats.numTxs)
	t.Logf("Number of key assignments: %v", stats.numKeyAssignments)
	t.Logf("Number of slashes: %v", stats.numSlashes)
	t.Logf("Average summed block time delta passed per trace: %v", stats.totalBlockTimePassedPerTrace/time.Duration(numTraces))
}

func RunItfTrace(t *testing.T, path string) {
	t.Helper()
	t.Logf("🟡 Testing trace %s", path)

	// Load trace
	trace := &itf.Trace{}
	if err := trace.LoadFromFile(path); err != nil {
		t.Fatalf("Error loading trace file: %s", err)
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
	// extra var names are ok, so no need to check inclusion the other way around

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

	// generate keys that can be assigned on consumers, according to the ConsumerAddresses in the trace
	consumerAddressesExpr := params["ConsumerAddresses"].Value.(itf.ListExprType)

	consumerValidators, _, consumerPrivVals, err := integration.CreateValidators(len(consumerAddressesExpr), "consumer")
	require.NoError(t, err, "Error creating consumer signers")

	// sort the keys of consumer priv vals for determinism
	// this is necessary because the order of the keys in the map is not deterministic
	// and the model and the system need to have the same order
	consumerPrivValKeys := make([]string, 0, len(consumerPrivVals))
	for key := range consumerPrivVals {
		consumerPrivValKeys = append(consumerPrivValKeys, key)
	}
	// sort the keys
	sort.Strings(consumerPrivValKeys)

	consumerAddrNamesToVals := make(map[string]*cmttypes.Validator, len(consumerAddressesExpr))
	consumerAddrNamesToPrivVals := make(map[string]cmttypes.PrivValidator, len(consumerAddressesExpr))
	realAddrsToModelConsAddrs := make(map[string]string, len(consumerAddressesExpr))
	for i := 0; i < len(consumerAddressesExpr); i++ {
		address := consumerPrivValKeys[i]
		privVal := consumerPrivVals[address]
		consumerAddrNamesToPrivVals[consumerAddressesExpr[i].Value.(string)] = privVal
		consumerAddrNamesToVals[consumerAddressesExpr[i].Value.(string)] = consumerValidators.Validators[i]
		realAddrsToModelConsAddrs[address] = consumerAddressesExpr[i].Value.(string)
	}

	// create params struct
	vscTimeout := time.Duration(params["VscTimeout"].Value.(int64)) * time.Second

	unbondingPeriodPerChain := make(map[ChainId]time.Duration, len(consumers))
	trustingPeriodPerChain := make(map[ChainId]time.Duration, len(consumers))
	ccvTimeoutPerChain := make(map[ChainId]time.Duration, len(consumers))
	for _, consumer := range chains {
		unbondingPeriodPerChain[ChainId(consumer)] = time.Duration(params["UnbondingPeriodPerChain"].Value.(itf.MapExprType)[consumer].Value.(int64)) * time.Second
		trustingPeriodPerChain[ChainId(consumer)] = time.Duration(params["TrustingPeriodPerChain"].Value.(itf.MapExprType)[consumer].Value.(int64)) * time.Second
		ccvTimeoutPerChain[ChainId(consumer)] = time.Duration(params["CcvTimeout"].Value.(itf.MapExprType)[consumer].Value.(int64)) * time.Second
	}
	downtimeSlashPercentage := sdk.NewDec(params["DowntimeSlashPercentage"].Value.(int64))
	doubleSignSlashPercentage := sdk.NewDec(params["DoubleSignSlashPercentage"].Value.(int64))
	downtimeJailDuration := time.Duration(params["DowntimeJailDuration"].Value.(int64)) * time.Second

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

	valSet, addressMap, signers, err := CreateValSet(initialValSet, "provider")
	require.NoError(t, err, "Error creating validator set")

	// get the set of signers for consumers: the validator signers, plus signers for the assignable addresses
	consumerSigners := make(map[string]cmttypes.PrivValidator, 0)
	for consAddr, consPrivVal := range consumerPrivVals {
		consumerSigners[consAddr] = consPrivVal
	}
	for consAddr, signer := range signers {
		consumerSigners[consAddr] = signer
	}

	// add the consumer validators to the address map
	for consAddr, consVal := range consumerAddrNamesToVals {
		addressMap[consAddr] = consVal
	}

	// get a slice of validators in the right order
	nodes := make([]*cmttypes.Validator, len(valNames))
	for i, valName := range valNames {
		nodes[i] = addressMap[valName]
	}

	// very hacky: the system produces a lot of extra blocks, e.g. when setting up consumer chains, when updating clients, etc.
	// to be able to compare the model to the system, we make the blocks per epoch a very large number (such that an epoch never ends naturally in the system while running the trace)
	// When an epoch in the model ends (which we can detect by the height modulo the epoch length), we produce many, many blocks in the system, such that an epoch actually ends.
	blocksPerEpoch := int64(200)
	modelBlocksPerEpoch := params["BlocksPerEpoch"].Value.(int64)

	driver := newDriver(t, nodes, valNames)
	driver.DriverStats = &stats

	driver.setupProvider(modelParams, valSet, signers, nodes, valNames)
	providerParams := driver.providerKeeper().GetParams(driver.providerCtx())
	providerParams.BlocksPerEpoch = blocksPerEpoch
	driver.providerKeeper().SetParams(driver.providerCtx(), providerParams)

	// begin enough blocks to end the first epoch
	for i := int64(1); i < blocksPerEpoch; i++ {
		driver.endAndBeginBlock("provider", 1*time.Nanosecond)
	}

	slashingParams := driver.providerSlashingKeeper().GetParams(driver.providerCtx())
	slashingParams.DowntimeJailDuration = downtimeJailDuration
	driver.providerSlashingKeeper().SetParams(driver.providerCtx(), slashingParams)

	modelVscIdsToActualPackets := make(map[uint64]types.ValidatorSetChangePacketData, 0)
	actualPacketIdsToModelVscIds := make(map[uint64]uint64, 0)

	// remember the time offsets to be able to compare times to the model
	// this is necessary because the system needs to do many steps to initialize the chains,
	// which is abstracted away in the model
	timeOffset := driver.runningTime("provider")

	t.Log("Started chains")

	t.Log("Reading the trace...")

	for index, state := range trace.States {
		t.Log("Height modulo epoch length:", driver.providerChain().CurrentHeader.Height%blocksPerEpoch)
		t.Log("Model height modulo epoch length:", ProviderHeight(state.VarValues["currentState"].Value.(itf.MapExprType))%modelBlocksPerEpoch)
		t.Logf("Reading state %v of trace %v", index, path)

		// store the height of the provider state before each step.
		// The height should only pass an epoch when it passes an epoch in the model, too,
		// otherwise there is an error, and blocksPerEpoch needs to be increased.
		// See the comment for blocksPerEpoch above.
		heightBeforeStep := driver.providerHeight()

		trace := state.VarValues["trace"].Value.(itf.ListExprType)
		// lastAction will get the last action that was executed so far along the model trace,
		// i.e. the action we should perform before checking model vs actual system equivalence
		lastAction := trace[len(trace)-1].Value.(itf.MapExprType)

		currentModelState := state.VarValues["currentState"].Value.(itf.MapExprType)

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

			stats.numTxs++
		case "EndAndBeginBlockForProvider":
			timeAdvancement := lastAction["timeAdvancement"].Value.(int64)
			consumersToStart := lastAction["consumersToStart"].Value.(itf.ListExprType)
			consumersToStop := lastAction["consumersToStop"].Value.(itf.ListExprType)
			t.Log("EndAndBeginBlockForProvider", timeAdvancement, consumersToStart, consumersToStop)

			stats.numStartedChains += len(consumersToStart)
			stats.numStops += len(consumersToStop)

			// get the block height in the model
			modelHeight := ProviderHeight(currentModelState)

			if modelHeight%modelBlocksPerEpoch == 0 {
				// in the model, an epoch ends, so we need to produce blocks in the system to get the actual height
				// to end an epoch with the first of the two subsequent calls to endAndBeginBlock below
				actualHeight := driver.providerHeight()

				heightInEpoch := actualHeight % blocksPerEpoch

				// produce blocks until the next block ends the epoch
				for i := heightInEpoch; i < blocksPerEpoch; i++ {
					driver.endAndBeginBlock("provider", 1*time.Nanosecond)
				}
			}

			// we need at least 2 blocks, because for a packet sent at height H, the receiving chain
			// needs a header of height H+1 to accept the packet
			// so, we do two blocks, one with a very small increment,
			// and then another to increment the rest of the time
			runningConsumersBefore := driver.runningConsumers()

			driver.endAndBeginBlock("provider", 1*time.Nanosecond)
			for _, consumer := range driver.runningConsumers() {
				UpdateProviderClientOnConsumer(t, driver, consumer.ChainId)
			}
			driver.endAndBeginBlock("provider", time.Duration(timeAdvancement)*time.Second-1*time.Nanosecond)

			runningConsumersAfter := driver.runningConsumers()

			// the consumers that were running before but not after must have timed out
			for _, consumer := range runningConsumersBefore {
				found := false
				for _, consumerAfter := range runningConsumersAfter {
					if consumerAfter.ChainId == consumer.ChainId {
						found = true
						break
					}
				}
				if !found {
					stats.numTimeouts++
				}
			}

			// save the last timestamp for runningConsumers,
			// because setting up chains will modify timestamps
			// when the coordinator is starting chains
			lastTimestamps := make(map[ChainId]time.Time, len(consumers))
			for _, consumer := range driver.runningConsumers() {
				lastTimestamps[ChainId(consumer.ChainId)] = driver.runningTime(ChainId(consumer.ChainId))
			}

			driver.coordinator.CurrentTime = driver.runningTime("provider")
			// start consumers
			for _, consumer := range consumersToStart {
				driver.setupConsumer(
					consumer.Value.(string),
					modelParams,
					driver.providerChain().Vals,
					consumerSigners,
					nodes,
					valNames,
					driver.providerChain(),
				)
			}

			// stop consumers
			for _, consumer := range consumersToStop {
				driver.stopConsumer(ChainId(consumer.Value.(string)))
			}

			// reset the times for the consumers that were not stopped or started just now
			// their times were messed up by the coordinator
			for consumer, timestamp := range lastTimestamps {
				driver.setTime(consumer, timestamp)
			}

			// for all connected consumers, update the clients...
			// unless it was the last consumer to be started, in which case it already has the header
			// as we called driver.setupConsumer
			for _, consumer := range driver.runningConsumers() {
				if len(consumersToStart) > 0 && consumer.ChainId == consumersToStart[len(consumersToStart)-1].Value.(string) {
					continue
				}

				UpdateProviderClientOnConsumer(t, driver, consumer.ChainId)
			}

		case "EndAndBeginBlockForConsumer":
			consumerChain := lastAction["consumerChain"].Value.(string)
			timeAdvancement := lastAction["timeAdvancement"].Value.(int64)
			t.Log("EndAndBeginBlockForConsumer", consumerChain, timeAdvancement)

			// as in EndAndBeginBlockForProvider, we need to produce 2 blocks,
			// while still honoring the time advancement
			headerBefore := driver.chain(ChainId(consumerChain)).LastHeader
			_ = headerBefore

			driver.endAndBeginBlock(ChainId(consumerChain), 1*time.Nanosecond)
			UpdateConsumerClientOnProvider(t, driver, consumerChain)

			driver.endAndBeginBlock(ChainId(consumerChain), time.Duration(timeAdvancement)*time.Second-1*time.Nanosecond)

			// update the client on the provider
			UpdateConsumerClientOnProvider(t, driver, consumerChain)

		case "DeliverVscPacket":
			consumerChain := lastAction["consumerChain"].Value.(string)
			t.Log("DeliverVscPacket", consumerChain)

			// delivering the packet should give an error
			// if the consumer is timed out in the model
			var expectError bool
			if ConsumerStatus(currentModelState, consumerChain) == TIMEDOUT_STATUS {
				expectError = true
				driver.DeliverPacketToConsumer(ChainId(consumerChain), expectError)

				// stop the consumer chain
				driver.providerKeeper().StopConsumerChain(driver.providerCtx(), consumerChain, expectError)
			} else {
				expectError = false
				driver.DeliverPacketToConsumer(ChainId(consumerChain), expectError)
			}
		case "DeliverPacketToProvider":
			consumerChain := lastAction["consumerChain"].Value.(string)
			t.Log("DeliverPacketToProvider", consumerChain)

			var expectError bool
			if ConsumerStatus(currentModelState, consumerChain) == TIMEDOUT_STATUS {
				expectError = true
				// expectError is true, because we expect the consumer to have timed out.
				// the call will fail if there is no error
				driver.DeliverPacketFromConsumer(ChainId(consumerChain), expectError)

				// stop the consumer chain on the provider
				driver.providerKeeper().StopConsumerChain(driver.providerCtx(), consumerChain, expectError)
			} else {
				expectError = false
				driver.DeliverPacketFromConsumer(ChainId(consumerChain), expectError)
			}
		case "KeyAssignment":
			consumerChain := lastAction["consumerChain"].Value.(string)
			node := lastAction["validator"].Value.(string)
			consumerAddr := lastAction["consumerAddr"].Value.(string)

			t.Log("KeyAssignment", consumerChain, node, consumerAddr)
			stats.numKeyAssignments++

			valIndex := getIndexOfString(node, valNames)
			assignedPrivVal := consumerAddrNamesToPrivVals[consumerAddr]
			assignedKey, err := assignedPrivVal.GetPubKey()
			require.NoError(t, err, "Error getting pubkey")

			protoPubKey, err := tmencoding.PubKeyToProto(assignedKey)
			require.NoError(t, err, "Error converting pubkey to proto")

			err = driver.AssignKey(ChainId(consumerChain), int64(valIndex), protoPubKey)
			require.NoError(t, err, "Error assigning key")
		case "ConsumerInitiatedSlash":
			consumerChain := lastAction["consumerChain"].Value.(string)
			validatorName := lastAction["validator"].Value.(string)
			vscId := lastAction["vscId"].Value.(int64)
			isDowntime := lastAction["isDowntime"].Value.(bool)
			t.Log("ConsumerInitiatedSlash", consumerChain, validatorName, vscId, isDowntime)

			stats.numSlashes++

			actualPacket, found := modelVscIdsToActualPackets[uint64(vscId)]
			if !found {
				log.Fatalf("Error loading trace file %s, step %v: could not find actual packet for vsc id %v",
					path, index, vscId)
			}

			val := addressMap[validatorName]
			valConsAddr := sdk.ConsAddress(val.Address)

			slashFraction := doubleSignSlashPercentage
			if isDowntime {
				slashFraction = downtimeSlashPercentage
			}

			err = driver.RequestSlash(
				ChainId(consumerChain),
				valConsAddr,
				isDowntime,
				actualPacket,
				slashFraction,
			)
			require.NoError(t, err, "Error requesting slash")

		default:
			log.Fatalf("Error loading trace file %s, step %v: do not know action type %s",
				path, index, actionKind)
		}

		// deliver all acks that are ready
		driver.DeliverAcks()

		if verbose {
			t.Logf("Current actual state: %s", driver.getStateString())
		}

		// check that the actual state is the same as the model state
		t.Logf("Comparing model state to actual state...")

		// compare the running consumers
		modelRunningConsumers := RunningConsumers(currentModelState)

		systemRunningConsumers := driver.runningConsumers()
		actualRunningConsumers := make([]string, len(systemRunningConsumers))
		for i, chain := range systemRunningConsumers {
			actualRunningConsumers[i] = chain.ChainId
		}

		// sort the slices so that we can compare them
		sort.Slice(modelRunningConsumers, func(i, j int) bool {
			return modelRunningConsumers[i] < modelRunningConsumers[j]
		})
		sort.Slice(actualRunningConsumers, func(i, j int) bool {
			return actualRunningConsumers[i] < actualRunningConsumers[j]
		})

		require.Equal(t, modelRunningConsumers, actualRunningConsumers, "Running consumers do not match")

		// check validator sets - provider current validator set should be the one from the staking keeper
		CompareValidatorSets(t, driver, currentModelState, actualRunningConsumers, realAddrsToModelConsAddrs)

		// check times - sanity check that the block times match the ones from the model
		CompareTimes(driver, actualRunningConsumers, currentModelState, timeOffset)

		// check sent packets: we check that the package queues in the model and the system have the same length.
		for _, consumer := range actualRunningConsumers {
			ComparePacketQueues(t, driver, currentModelState, consumer, timeOffset)
		}
		// compare that the sent packets on the proider match the model
		CompareSentPacketsOnProvider(driver, currentModelState, timeOffset)

		// ensure that the jailed validators are the same in the model and the system,
		// and that the jail end times are the same, in particular
		CompareJailedValidators(driver, currentModelState, timeOffset, addressMap)

		// for all newly sent vsc packets, figure out which vsc id in the model they correspond to
		for _, consumer := range actualRunningConsumers {
			actualPackets := driver.packetQueue(PROVIDER, ChainId(consumer))
			actualNewPackets := make([]types.ValidatorSetChangePacketData, 0)
			for _, packet := range actualPackets {

				var packetData types.ValidatorSetChangePacketData
				err := types.ModuleCdc.UnmarshalJSON(packet.Packet.GetData(), &packetData)
				require.NoError(t, err, "Error unmarshalling packet data")

				actualVscId := packetData.ValsetUpdateId
				if _, ok := actualPacketIdsToModelVscIds[actualVscId]; ok {
					// we already handled this packet previously; continue
					continue
				}
				actualNewPackets = append(actualNewPackets, packetData)
			}

			modelPackets := PacketQueue(currentModelState, PROVIDER, consumer)
			newModelVscIds := make([]uint64, 0)
			for _, packet := range modelPackets {
				modelVscId := uint64(packet.Value.(itf.MapExprType)["value"].Value.(itf.MapExprType)["id"].Value.(int64))
				if _, ok := modelVscIdsToActualPackets[modelVscId]; ok {
					// we already handled this packet previously; continue
					continue
				}
				newModelVscIds = append(newModelVscIds, modelVscId)
			}

			// sort the new packets by vsc id
			sort.Slice(actualNewPackets, func(i, j int) bool {
				return actualNewPackets[i].ValsetUpdateId < actualNewPackets[j].ValsetUpdateId
			})
			sort.Slice(newModelVscIds, func(i, j int) bool {
				return newModelVscIds[i] < newModelVscIds[j]
			})

			// map the actual packets to the model ids
			for i, actualPacket := range actualNewPackets {
				modelVscIdsToActualPackets[newModelVscIds[i]] = actualPacket
				actualPacketIdsToModelVscIds[actualPacket.ValsetUpdateId] = newModelVscIds[i]
			}
		}

		stats.EnterStats(driver)

		// should not have ended an epoch, unless we also ended an epoch in the model
		heightAfterStep := driver.providerHeight()

		if heightBeforeStep/blocksPerEpoch != heightAfterStep/blocksPerEpoch {
			// we changed epoch during this step, so ensure that the model also changed epochs
			require.True(t, ProviderHeight(state.VarValues["currentState"].Value.(itf.MapExprType))%modelBlocksPerEpoch == 0, "Height in model did not change epoch, but did in system. increase blocksPerEpoch in the system")
		}

		t.Logf("State %v of trace %v is ok!", index, path)
	}
	t.Log("🟢 Trace is ok!")
}

func UpdateProviderClientOnConsumer(t *testing.T, driver *Driver, consumerChainId string) {
	t.Helper()
	driver.path(ChainId(consumerChainId)).AddClientHeader(PROVIDER, driver.providerHeader())
	err := driver.path(ChainId(consumerChainId)).UpdateClient(consumerChainId, false)
	require.True(t, err == nil, "Error updating client from %v on provider: %v", consumerChainId, err)
}

func UpdateConsumerClientOnProvider(t *testing.T, driver *Driver, consumerChain string) {
	t.Helper()
	consumerHeader := driver.chain(ChainId(consumerChain)).LastHeader
	driver.path(ChainId(consumerChain)).AddClientHeader(consumerChain, consumerHeader)
	err := driver.path(ChainId(consumerChain)).UpdateClient(PROVIDER, false)
	require.True(t, err == nil, "Error updating client from %v on provider: %v", consumerChain, err)
}

func CompareValidatorSets(
	t *testing.T,
	driver *Driver,
	currentModelState map[string]itf.Expr,
	consumers []string,
	// a map from real addresses to the names of those consumer addresses in the model
	keyAddrsToModelConsAddrName map[string]string,
) {
	t.Helper()
	modelValSet := ValidatorSet(currentModelState, "provider")

	rawActualValSet := driver.providerValidatorSet()

	actualValSet := make(map[string]int64, len(rawActualValSet))

	for _, val := range rawActualValSet {
		valName := val.Description.Moniker
		actualValSet[valName] = val.Tokens.Int64()
	}

	require.NoError(t, CompareValSet(modelValSet, actualValSet), "Validator sets do not match")

	for _, consumer := range consumers {
		modelValSet = HistoricalValidatorSet(currentModelState, consumer, 0)

		consumerVals := driver.consumerValidatorSet(ChainId(consumer))
		consumerCurValSet := make(map[string]int64, len(consumerVals))
		for _, val := range consumerVals {
			pubkey, err := val.ConsPubKey()
			require.NoError(t, err, "Error getting pubkey")

			consAddrModelName, ok := keyAddrsToModelConsAddrName[pubkey.Address().String()]
			if ok { // the node has a key assigned, use the name of the consumer address in the model
				consumerCurValSet[consAddrModelName] = val.Power
			} else { // the node doesn't have a key assigned yet, get the validator moniker
				consAddr := providertypes.NewConsumerConsAddress(sdk.ConsAddress(pubkey.Address().Bytes()))

				// the consumer vals right now are CrossChainValidators, for which we don't know their mnemonic
				// so we need to find the mnemonic of the consumer val now to enter it by name in the map

				// get the address on the provider that corresponds to the consumer address
				providerConsAddr, found := driver.providerKeeper().GetValidatorByConsumerAddr(driver.providerCtx(), consumer, consAddr)
				if !found {
					providerConsAddr = providertypes.NewProviderConsAddress(consAddr.Address)
				}

				// get the validator for that address on the provider
				providerVal, found := driver.providerStakingKeeper().GetValidatorByConsAddr(driver.providerCtx(), providerConsAddr.Address)
				require.True(t, found, "Error getting provider validator")

				// use the moniker of that validator
				consumerCurValSet[providerVal.GetMoniker()] = val.Power
			}
		}
		require.NoError(t, CompareValSet(modelValSet, consumerCurValSet), "Validator sets do not match for consumer %v", consumer)
	}
}

// ComparePacketQueues compares the packet queues in the model to the packet queues in the system.
// It compares both incoming (provider->consumer) and outgoing (consumer->provider) packets.
// It takes the number of packets into account, as well as the timeout timestamp on each packet.
// Other fields are not compared.
func ComparePacketQueues(
	t *testing.T,
	driver *Driver,
	currentModelState map[string]itf.Expr,
	consumer string,
	timeOffset time.Time,
) {
	t.Helper()
	ComparePacketQueue(t, driver, currentModelState, PROVIDER, consumer, timeOffset)
	ComparePacketQueue(t, driver, currentModelState, consumer, PROVIDER, timeOffset)
}

func ComparePacketQueue(
	t *testing.T,
	driver *Driver,
	currentModelState map[string]itf.Expr,
	sender string,
	receiver string,
	timeOffset time.Time,
) {
	t.Helper()
	modelSenderQueue := PacketQueue(currentModelState, sender, receiver)
	actualSenderQueue := driver.packetQueue(ChainId(sender), ChainId(receiver))

	actualPacketStrings := make([]string, len(actualSenderQueue))
	for i, packet := range actualSenderQueue {
		actualPacketStrings[i] = string(packet.Packet.GetData())
	}

	require.Equal(t,
		len(modelSenderQueue),
		len(actualSenderQueue),
		"Packet queue sizes do not match for sender %v, receiver %v.\n model: %v\n actual: %v",
		sender,
		receiver,
		pretty.Sprint(modelSenderQueue),
		pretty.Sprint(actualPacketStrings))

	for i := range modelSenderQueue {
		actualPacket := actualSenderQueue[i]
		modelPacket := modelSenderQueue[i].Value.(itf.MapExprType)["value"].Value.(itf.MapExprType)

		actualTimeout := time.Unix(0, int64(actualPacket.Packet.TimeoutTimestamp)).Unix() - timeOffset.Unix()
		modelTimeout := GetTimeoutForPacket(modelPacket)

		require.Equal(t,
			modelTimeout,
			actualTimeout,
			"Timeouts do not match for packet %v, sender %v, receiver %v",
			actualPacket,
			sender,
			receiver)
	}
}

// CompareTimes compares the block times in the model to the block times in the system.
// It takes into account the timeOffsets, which should be the starting times
// of the chains in the system after the system has been initialized.
// We only compare down to seconds, because the model and system will differ
// on the order of nanoseconds.
// In more detail, the model will have timestamp `X seconds, 0 nanoseconds`,
// and the actual system will have timestamp `X seconds, Y nanoseconds`,
// where Y roughly depends on how many extra blocks needed to be produced
// when setting up consumer chains.
// Note: If Y gets too large, the check might fail, even though it should not.
// This will happen if on the order of 10^8 consumer chains
// are started during the execution of a trace.
func CompareTimes(
	driver *Driver,
	consumers []string,
	currentModelState map[string]itf.Expr,
	timeOffset time.Time,
) (err error) {
	providerRunningTimestamp := RunningTime(currentModelState, "provider")
	actualRunningProviderTime := driver.runningTime("provider")

	if providerRunningTimestamp != actualRunningProviderTime.Unix()-timeOffset.Unix() {
		return fmt.Errorf("Running times do not match for provider")
	}

	for _, chain := range consumers {
		modelRunningTimestamp := RunningTime(currentModelState, chain)
		actualRunningChainTime := driver.runningTime(ChainId(chain))

		if modelRunningTimestamp != actualRunningChainTime.Unix()-timeOffset.Unix() {
			return fmt.Errorf("Running times do not match for chain %v", chain)
		}
	}
	return nil
}

// CompareValSet compares the validator set in the model to the validator set in the system.
// The model validator set is given as a map from validator name to power,
// whereas the system validator set is given as a slice of validators.
// The names in the model validator set are expected to correspond to the monikers in the system validator set.
func CompareValSet(modelValSet map[string]itf.Expr, systemValSet map[string]int64) error {
	expectedValSet := make(map[string]int64, len(modelValSet))
	// strip away vals with power 0, because they don't matter for the comparison
	for val, power := range modelValSet {
		if power.Value.(int64) == 0 {
			continue
		}
		expectedValSet[val] = power.Value.(int64)
	}

	actualValSet := make(map[string]int64, len(systemValSet))
	for val, power := range systemValSet {
		if power == 0 {
			continue
		}
		actualValSet[val] = power
	}

	if !reflect.DeepEqual(expectedValSet, actualValSet) {
		return fmt.Errorf("Validator sets do not match: (- expected, + actual): %v", pretty.Compare(expectedValSet, actualValSet))
	}
	return nil
}

func CompareSentPacketsOnProvider(driver *Driver, currentModelState map[string]itf.Expr, timeOffset time.Time) {
	for _, consumer := range driver.runningConsumers() {
		vscSendTimestamps := driver.providerKeeper().GetAllVscSendTimestamps(driver.providerCtx(), consumer.ChainId)

		actualVscSendTimestamps := make([]time.Time, 0)
		for _, vscSendTimestamp := range vscSendTimestamps {
			actualVscSendTimestamps = append(actualVscSendTimestamps, vscSendTimestamp.Timestamp)
		}

		modelVscSendTimestamps := VscSendTimestamps(currentModelState, consumer.ChainId)

		for i, modelVscSendTimestamp := range modelVscSendTimestamps {
			actualTimeWithOffset := actualVscSendTimestamps[i].Unix() - timeOffset.Unix()
			require.Equal(
				driver.t,
				modelVscSendTimestamp,
				actualTimeWithOffset,
				"Vsc send timestamps do not match for consumer %v",
				consumer.ChainId,
			)
		}
	}
}

func CompareJailedValidators(
	driver *Driver,
	currentModelState map[string]itf.Expr,
	timeOffset time.Time,
	modelNamesToSystemConsAddr map[string]*cmttypes.Validator,
) {
	modelJailedVals, modelJailEndTimes := ProviderJailedValidators(currentModelState)

	for i, modelJailedVal := range modelJailedVals {
		modelJailEndTime := modelJailEndTimes[i]

		valConsAddr := sdk.ConsAddress(modelNamesToSystemConsAddr[modelJailedVal].Address)
		valSigningInfo, found := driver.providerSlashingKeeper().GetValidatorSigningInfo(driver.providerCtx(), valConsAddr)
		require.True(driver.t, found, "Error getting signing info for validator %v", modelJailedVal)

		systemJailEndTime := valSigningInfo.JailedUntil
		actualTimeWithOffset := systemJailEndTime.Unix() - timeOffset.Unix()

		require.Equal(
			driver.t,
			modelJailEndTime,
			actualTimeWithOffset,
			"Jail end times do not match for validator %v",
			modelJailedVal,
		)
	}

	// build a convenient list of validator signing infos
	validatorsSigningInfos := make([]slashingtypes.ValidatorSigningInfo, 0)
	driver.providerSlashingKeeper().IterateValidatorSigningInfos(
		driver.providerCtx(),
		func(_ sdk.ConsAddress, valSigningInfo slashingtypes.ValidatorSigningInfo) (stop bool) {
			validatorsSigningInfos = append(validatorsSigningInfos, valSigningInfo)
			return false
		},
	)
}

func (s *Stats) EnterStats(driver *Driver) {
	// highest observed voting power
	for _, val := range driver.providerValidatorSet() {
		if val.Tokens.Int64() > s.highestObservedValPower {
			s.highestObservedValPower = val.Tokens.Int64()
		}
	}

	// max number of in-flight packets
	inFlightPackets := 0
	for _, consumer := range driver.runningConsumers() {
		inFlightPackets += len(driver.packetQueue(PROVIDER, ChainId(consumer.ChainId)))
		inFlightPackets += len(driver.packetQueue(ChainId(consumer.ChainId), PROVIDER))
	}
	if inFlightPackets > s.maxNumInFlightPackets {
		s.maxNumInFlightPackets = inFlightPackets
	}
}
