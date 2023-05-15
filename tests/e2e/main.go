package main

import (
	"bufio"
	"flag"
	"fmt"
	"log"
	"os/exec"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/kylelemons/godebug/pretty"
)

var (
	verbose              = flag.Bool("verbose", false, "turn verbose logging on/off")
	happyPathOnly        = flag.Bool("happy-path-only", false, "run happy path tests only")
	includeMultiConsumer = flag.Bool("include-multi-consumer", false, "include multiconsumer tests in run")
	parallel             = flag.Bool("parallel", false, "run all tests in parallel")
	localSdkPath         = flag.String("local-sdk-path", "",
		"path of a local sdk version to build and reference in integration tests")
)

var (
	useGaia = flag.Bool("use-gaia", false, "use gaia instead of ICS provider app")
	gaiaTag = flag.String("gaia-tag", "", "gaia tag to use - default is latest")
)

// runs E2E tests
// all docker containers are built sequentially to avoid race conditions when using local cosmos-sdk
// after building docker containers, all tests are run in parallel using their respective docker containers
func main() {
	flag.Parse()

	if happyPathOnly != nil && *happyPathOnly {
		fmt.Println("=============== running happy path only ===============")
		tr := DefaultTestRun()
		tr.Run(happyPathSteps, *localSdkPath, *useGaia, *gaiaTag)
		return
	}

	testRuns := []testRunWithSteps{
		{DefaultTestRun(), happyPathSteps},
		// {DemocracyTestRun(), democracySteps},
		{SlashThrottleTestRun(), slashThrottleSteps},
	}
	if includeMultiConsumer != nil && *includeMultiConsumer {
		testRuns = append(testRuns, testRunWithSteps{MultiConsumerTestRun(), multipleConsumers})
	}

	start := time.Now()
	if parallel != nil && *parallel {
		fmt.Println("=============== running all tests in parallel ===============")
		var wg sync.WaitGroup
		for _, run := range testRuns {
			wg.Add(1)
			go func(run testRunWithSteps) {
				defer wg.Done()
				tr := run.testRun
				tr.Run(run.steps, *localSdkPath, *useGaia, *gaiaTag)
			}(run)
		}
		wg.Wait()
		fmt.Printf("TOTAL TIME ELAPSED: %v\n", time.Since(start))
		return
	}

	for _, run := range testRuns {
		tr := run.testRun
		tr.Run(run.steps, *localSdkPath, *useGaia, *gaiaTag)
	}
	fmt.Printf("TOTAL TIME ELAPSED: %v\n", time.Since(start))
}

// Run sets up docker container and executes the steps in the test run.
// Docker containers are torn down after the test run is complete.
func (tr *TestRun) Run(steps []Step, localSdkPath string, useGaia bool, gaiaTag string) {
	tr.SetDockerConfig(localSdkPath, useGaia, gaiaTag)

	tr.validateStringLiterals()
	tr.startDocker()
	tr.executeSteps(steps)
	tr.teardownDocker()
}

type testRunWithSteps struct {
	testRun TestRun
	steps   []Step
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
	case submitEquivocationProposalAction:
		tr.submitEquivocationProposal(action, verbose)
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
	case startHermesAction:
		tr.startHermes(action, verbose)
	default:
		log.Fatalf("unknown action in testRun %s: %#v", tr.name, action)
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

// executeSteps sequentially runs steps.
func (tr *TestRun) executeSteps(steps []Step) {
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
	localSdk := tr.localSdkPath
	if localSdk == "" {
		localSdk = "default"
	}
	useGaia := "false"
	gaiaTag := ""
	if tr.useGaia {
		useGaia = "true"
		if tr.gaiaTag != "" {
			majVersion, err := strconv.Atoi(tr.gaiaTag[1:strings.Index(tr.gaiaTag, ".")])
			if err != nil {
				panic(fmt.Sprintf("invalid gaia version %s", tr.gaiaTag))
			}
			if majVersion < 9 {
				panic(fmt.Sprintf("gaia version %s is not supported - supporting only v9.x.x and newer", tr.gaiaTag))
			}
			gaiaTag = tr.gaiaTag
		}
	}
	scriptStr := fmt.Sprintf(
		"tests/e2e/testnet-scripts/start-docker.sh %s %s %s %s %s",
		tr.containerConfig.containerName,
		tr.containerConfig.instanceName,
		localSdk,
		useGaia,
		gaiaTag,
	)

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
