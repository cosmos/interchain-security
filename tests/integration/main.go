package main

import (
	"bufio"
	"flag"
	"fmt"
	"log"
	"os/exec"
	"reflect"
	"sync"
	"time"

	"github.com/kylelemons/godebug/pretty"
)

var verbose = flag.Bool("verbose", false, "turn verbose logging on/off")
var happyPathOnly = flag.Bool("happy-path-only", false, "run happy path tests only")
var multiconsumer = flag.Bool("multiconsumer", false, "include multiconsumer tests in run")
var localSdkPath = flag.String("local-sdk-path", "",
	"path of a local sdk version to build and reference in integration tests")

// runs integration tests
// all docker containers are built sequentially to avoid race conditions when using local cosmos-sdk
// after building docker containers, all tests are run in parallel using their respective docker containers
func main() {
	flag.Parse()

	if happyPathOnly != nil && *happyPathOnly {
		tr := DefaultTestRun()
		tr.SetLocalSDKPath(*localSdkPath)
		tr.ValidateStringLiterals()
		tr.startDocker()
		tr.ExecuteSteps(happyPathSteps)
		tr.teardownDocker()
		return
	}

	start := time.Now()
	tr := DefaultTestRun()
	tr.SetLocalSDKPath(*localSdkPath)
	tr.ValidateStringLiterals()
	tr.startDocker()
	tr.ExecuteSteps(happyPathSteps)
	tr.teardownDocker()

	dmc := DemocracyTestRun()
	dmc.SetLocalSDKPath(*localSdkPath)
	dmc.ValidateStringLiterals()
	dmc.startDocker()
	dmc.ExecuteSteps(democracySteps)
	dmc.teardownDocker()

	slash := SlashThrottleTestRun()
	slash.SetLocalSDKPath(*localSdkPath)
	slash.ValidateStringLiterals()
	slash.startDocker()
	slash.ExecuteSteps(slashThrottleSteps)
	slash.teardownDocker()

	if multiconsumer != nil && *multiconsumer {
		mul := MultiConsumerTestRun()
		mul.SetLocalSDKPath(*localSdkPath)
		mul.ValidateStringLiterals()
		mul.startDocker()
		mul.ExecuteSteps(multipleConsumers)
		slash.teardownDocker()
	}

	fmt.Printf("TOTAL TIME ELAPSED: %v\n", time.Since(start))
}

func (tr *TestRun) runStep(step Step, verbose bool) {
	switch action := step.action.(type) {
	case StartChainAction:
		tr.startChain(action, verbose)
	case SendTokensAction:
		tr.sendTokens(action, verbose)
	case submitTextProposalAction:
		tr.submitTextProposal(action, verbose)
	case submitConsumerAdditionProposalAction:
		tr.submitConsumerAdditionProposal(action, verbose)
	case submitConsumerRemovalProposalAction:
		tr.submitConsumerRemovalProposal(action, verbose)
	case submitParamChangeProposalAction:
		tr.submitParamChangeProposal(action, verbose)
	case voteGovProposalAction:
		tr.voteGovProposal(action, verbose)
	case startConsumerChainAction:
		tr.startConsumerChain(action, verbose)
	case addChainToRelayerAction:
		tr.addChainToRelayer(action, verbose)
	case addIbcConnectionAction:
		tr.addIbcConnection(action, verbose)
	case addIbcChannelAction:
		tr.addIbcChannel(action, verbose)
	case transferChannelCompleteAction:
		tr.transferChannelComplete(action, verbose)
	case relayPacketsAction:
		tr.relayPackets(action, verbose)
	case relayRewardPacketsToProviderAction:
		tr.relayRewardPacketsToProvider(action, verbose)
	case delegateTokensAction:
		tr.delegateTokens(action, verbose)
	case unbondTokensAction:
		tr.unbondTokens(action, verbose)
	case redelegateTokensAction:
		tr.redelegateTokens(action, verbose)
	case downtimeSlashAction:
		tr.invokeDowntimeSlash(action, verbose)
	case unjailValidatorAction:
		tr.unjailValidator(action, verbose)
	case doublesignSlashAction:
		tr.invokeDoublesignSlash(action, verbose)
	case registerRepresentativeAction:
		tr.registerRepresentative(action, verbose)
	case assignConsumerPubKeyAction:
		tr.assignConsumerPubKey(action, verbose)
	case slashThrottleDequeue:
		tr.waitForSlashThrottleDequeue(action, verbose)
	default:
		log.Fatalf(fmt.Sprintf(`unknown action in testRun %s: %#v`, tr.name, action))
	}

	modelState := step.state
	actualState := tr.getState(step.state)

	// Check state
	if !reflect.DeepEqual(actualState, modelState) {
		fmt.Printf("=============== %s FAILED ===============\n", tr.name)
		fmt.Println("FAILED action", reflect.TypeOf(step.action).Name())
		pretty.Print("actual state", actualState)
		pretty.Print("model state", modelState)
		log.Fatal(`actual state (-) not equal to model state (+): ` + pretty.Compare(actualState, modelState))
	}
}

// ExecuteStepsInWaitGroup runs steps in a WaitGroup so that the test run can be run in parallel.
func (tr *TestRun) ExecuteStepsInWaitGroup(wg *sync.WaitGroup, steps []Step) {
	defer wg.Done()
	tr.ExecuteSteps(steps)
}

// ExecuteSteps sequentially runs steps.
func (tr *TestRun) ExecuteSteps(steps []Step) {
	fmt.Printf("=============== started %s tests ===============\n", tr.name)

	start := time.Now()
	for i, step := range steps {
		// print something the show the test is alive
		fmt.Printf("running %s: step %d == %s \n",
			tr.name, i+1, reflect.TypeOf(step.action).Name())
		tr.runStep(step, *verbose)
	}

	fmt.Printf("=============== finished %s tests in %v ===============\n", tr.name, time.Since(start))
}

func (tr *TestRun) startDocker() {
	fmt.Printf("=============== building %s testRun ===============\n", tr.name)
	scriptStr := "tests/integration/testnet-scripts/start-docker.sh " +
		tr.containerConfig.containerName + " " +
		tr.containerConfig.instanceName + " " +
		tr.localSdkPath
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("/bin/bash", "-c", scriptStr)

	cmdReader, err := cmd.StdoutPipe()
	if err != nil {
		log.Fatal(err)
	}
	cmd.Stderr = cmd.Stdout

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	scanner := bufio.NewScanner(cmdReader)

	for scanner.Scan() {
		out := scanner.Text()
		if verbose != nil && *verbose {
			fmt.Println("startDocker: " + out)
		}
		if out == "beacon!!!!!!!!!!" {
			return
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}

	err = cmd.Wait()
	log.Fatalf("StartDocker exited with error: %v", err)
}

// remove docker container to reduce resource usage
// otherwise the chain will keep running in the background
func (tr *TestRun) teardownDocker() {
	fmt.Printf("===============  tearing down %s testRun ===============\n", tr.name)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "kill", tr.containerConfig.instanceName)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}
