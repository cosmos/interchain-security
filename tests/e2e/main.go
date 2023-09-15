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
	"golang.org/x/exp/slices"
)

// The list of test cases to be executed
type TestSet []string

func (t *TestSet) Set(value string) (err error) {
	// Check and skip duplicates
	for _, v := range *t {
		if v == value {
			return
		}
	}
	*t = append(*t, value)
	return
}

func (t *TestSet) String() string {
	return fmt.Sprint(*t)
}

var (
	verbose              = flag.Bool("verbose", false, "turn verbose logging on/off")
	includeMultiConsumer = flag.Bool("include-multi-consumer", false, "include multiconsumer tests in run")
	parallel             = flag.Bool("parallel", false, "run all tests in parallel")
	localSdkPath         = flag.String("local-sdk-path", "",
		"path of a local sdk version to build and reference in integration tests")
	useCometmock = flag.Bool("use-cometmock", false, "use cometmock instead of CometBFT. see https://github.com/informalsystems/CometMock")
	useGorelayer = flag.Bool("use-gorelayer", false, "use go relayer instead of Hermes")
)

var (
	useGaia = flag.Bool("use-gaia", false, "use gaia instead of ICS provider app")
	gaiaTag = flag.String("gaia-tag", "", "gaia tag to use - default is latest")
)

var (
	testSelection TestSet
	testRuns      = map[string]TestRunChoice{
		"default":          {name: "default", testRun: DefaultTestRun(), description: "default test run"},
		"changeover":       {name: "changeover", testRun: ChangeoverTestRun(), description: "changeover test run"},
		"democracy":        {name: "democracy", testRun: DemocracyTestRun(false), description: "democracy test run"},
		"democracy-reward": {name: "democracy-reward", testRun: DemocracyTestRun(true), description: "democracy test run with rewards"},
		"slash-throttle":   {name: "slash-throttle", testRun: SlashThrottleTestRun(), description: "slash throttle test run"},
		"multiconsumer":    {name: "multiconsumer", testRun: MultiConsumerTestRun(), description: "multi consumer test run"},
	}
	// helper function to get the test run choices by matching test runs
)

var stepChoices = map[string]StepChoice{
	"happy-path-short": {
		name:        "happy-path-short",
		steps:       shortHappyPathSteps,
		description: `This is like the happy path, but skips steps that involve starting or stopping nodes for the same chain outside of the chain setup or teardown. This is suited for CometMock+Gorelayer testing`,
		testRuns:    []string{"default"},
	},
	"light-client-attack": {
		name:        "light-client-attack",
		steps:       lightClientAttackSteps,
		description: `This is like the short happy path, but will slash validators for LightClientAttackEvidence instead of DuplicateVoteEvidence. This is suited for CometMock+Gorelayer testing, but currently does not work with CometBFT, since causing light client attacks is not implemented`,
		testRuns:    []string{"default"},
	},
	"happy-path": {
		name:        "happy-path",
		steps:       happyPathSteps,
		description: "happy path tests",
		testRuns:    []string{"default"},
	},
	"changeover": {
		name:        "changeover",
		steps:       changeoverSteps,
		description: "changeover tests",
		testRuns:    []string{"changeover"},
	},
	"democracy-reward": {
		name:        "democracy-reward",
		steps:       democracySteps,
		description: "democracy tests allowing rewards",
		testRuns:    []string{"democracy-reward"},
	},
	"democracy": {
		name:        "democracy",
		steps:       rewardDenomConsumerSteps,
		description: "democracy tests",
		testRuns:    []string{"democracy"},
	},
	"slash-throttle": {
		name:        "slash-throttle",
		steps:       slashThrottleSteps,
		description: "slash throttle tests",
		testRuns:    []string{"slash-throttle"},
	},
	"multiconsumer": {
		name:        "multiconsumer",
		steps:       multipleConsumers,
		description: "multi consumer tests",
		testRuns:    []string{"multiconsumer"},
	},
}

func executeTests(tests []testRunWithSteps) (err error) {
	if parallel != nil && *parallel {
		fmt.Println("=============== running all tests in parallel ===============")
	}

	var wg sync.WaitGroup
	for _, testCase := range tests {
		if parallel != nil && *parallel {
			wg.Add(1)
			go func(run testRunWithSteps) {
				defer wg.Done()
				run.testRun.Run(run.steps, *localSdkPath, *useGaia, *gaiaTag)
			}(testCase)
		} else {
			log.Printf("=============== running %s ===============\n", testCase.testRun.name)
			testCase.testRun.Run(testCase.steps, *localSdkPath, *useGaia, *gaiaTag)
		}
	}

	if parallel != nil && *parallel {
		wg.Wait()
	}
	return
}

func getTestCaseUsageString() string {
	var builder strings.Builder

	// Test case selection
	builder.WriteString("Test case selection:\nSelection of test steps to be executed:\n")
	for _, stepChoice := range stepChoices {
		builder.WriteString(fmt.Sprintf("- %s : %s. Compatible with test runners: %s\n", stepChoice.name, stepChoice.description, strings.Join(stepChoice.testRuns, ",")))
	}
	builder.WriteString("\n")

	// Test runner selection
	builder.WriteString("Test runner selection:\nSelection of test runners to be executed:\n")
	for _, testRunChoice := range testRuns {
		builder.WriteString(fmt.Sprintf("- %s : %s\n", testRunChoice.name, testRunChoice.description))
	}
	builder.WriteString("\n")

	// Example
	builder.WriteString("Example: -tc multiconsumer/multiconsumer -tc happy-path/default")

	return builder.String()
}

func parseArguments() (err error) {
	flag.Var(&testSelection, "tc",
		getTestCaseUsageString())
	flag.Parse()

	// Enforce go-relayer in case of cometmock as hermes is not yet supported
	if useCometmock != nil && *useCometmock && (useGorelayer == nil || !*useGorelayer) {
		fmt.Println("Enforcing go-relayer as cometmock is requested")
		if err = flag.Set("use-gorelayer", "true"); err != nil {
			return err
		}
	}
	return nil
}

type testRunWithSteps struct {
	testRun TestRun
	steps   []Step
}

func getTestCases(selection TestSet) (tests []testRunWithSteps) {
	// Run default tests if no test cases were selected
	if len(selection) == 0 {
		selection = TestSet{
			"changeover/changeover", "happy-path/default",
			"democracy-reward/democracy-reward", "democracy/democracy", "slash-throttle/slash-throttle",
		}
		if includeMultiConsumer != nil && *includeMultiConsumer {
			selection = append(selection, "multiconsumer/multiconsumer")
		}
	}

	// Get tests from selection
	tests = []testRunWithSteps{}
	for _, tc := range selection {
		// first part of tc is the test runner, second part is the test case
		splitTcString := strings.Split(tc, "/")
		if len(splitTcString) != 2 {
			log.Fatalf("Test case '%s' is invalid.\nsee usage info:\n%s", tc, getTestCaseUsageString())
		}
		stepsName := splitTcString[0]
		testRunnerName := splitTcString[1]

		if _, exists := stepChoices[stepsName]; !exists {
			log.Fatalf("Step choice '%s' not found.\nsee usage info:\n%s", tc, getTestCaseUsageString())
		}

		stepChoice := stepChoices[stepsName]

		if _, exists := testRuns[testRunnerName]; !exists {
			log.Fatalf("Test runner '%s' not found.\nsee usage info:\n%s", testRunnerName, getTestCaseUsageString())
		}

		testRunChoice := testRuns[testRunnerName]

		if !slices.Contains(stepChoice.testRuns, testRunChoice.name) {
			log.Fatalf("Step choice '%s' is not compatible with test runner '%s'. compatible test runs: %s", stepsName, testRunnerName, strings.Join(stepChoice.testRuns, ","))
		}

		tests = append(tests, testRunWithSteps{
			testRun: testRunChoice.testRun,
			steps:   stepChoice.steps,
		},
		)
	}
	return tests
}

// runs E2E tests
// all docker containers are built sequentially to avoid race conditions when using local cosmos-sdk
// after building docker containers, all tests are run in parallel using their respective docker containers
func main() {
	if err := parseArguments(); err != nil {
		flag.Usage()
		log.Fatalf("Error parsing command arguments %s\n", err)
	}

	testCases := getTestCases(testSelection)

	start := time.Now()
	err := executeTests(testCases)
	if err != nil {
		log.Fatalf("Test execution failed '%s'", err)
	}
	log.Printf("TOTAL TIME ELAPSED: %v\n", time.Since(start))
}

// Run sets up docker container and executes the steps in the test run.
// Docker containers are torn down after the test run is complete.
func (tr *TestRun) Run(steps []Step, localSdkPath string, useGaia bool, gaiaTag string) {
	tr.SetDockerConfig(localSdkPath, useGaia, gaiaTag)
	tr.SetCometMockConfig(*useCometmock)
	tr.SetRelayerConfig(*useGorelayer)

	tr.validateStringLiterals()
	tr.startDocker()
	tr.executeSteps(steps)
	tr.teardownDocker()
}

type StepChoice struct {
	name        string
	steps       []Step
	description string
	// contains the names of the test runs that are compatible with this step choice
	testRuns []string
}

type TestRunChoice struct {
	name        string
	testRun     TestRun
	description string
}

func (tr *TestRun) runStep(step Step, verbose bool) {
	switch action := step.Action.(type) {
	case StartChainAction:
		tr.startChain(action, verbose)
	case StartSovereignChainAction:
		tr.startSovereignChain(action, verbose)
	case LegacyUpgradeProposalAction:
		tr.submitLegacyUpgradeProposal(action, verbose)
	case waitUntilBlockAction:
		tr.waitUntilBlockOnChain(action)
	case ChangeoverChainAction:
		tr.changeoverChain(action, verbose)
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
	case submitParamChangeLegacyProposalAction:
		tr.submitParamChangeProposal(action, verbose)
	case voteGovProposalAction:
		tr.voteGovProposal(action, verbose)
	case startConsumerChainAction:
		tr.startConsumerChain(action, verbose)
	case addChainToRelayerAction:
		tr.addChainToRelayer(action, verbose)
	case createIbcClientsAction:
		tr.createIbcClientsHermes(action, verbose)
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
	case cancelUnbondTokensAction:
		tr.cancelUnbondTokens(action, verbose)
	case redelegateTokensAction:
		tr.redelegateTokens(action, verbose)
	case downtimeSlashAction:
		tr.invokeDowntimeSlash(action, verbose)
	case unjailValidatorAction:
		tr.unjailValidator(action, verbose)
	case doublesignSlashAction:
		tr.invokeDoublesignSlash(action, verbose)
	case lightClientAmnesiaAttackAction:
		tr.lightClientAmnesiaAttack(action, verbose)
	case lightClientEquivocationAttackAction:
		tr.lightClientEquivocationAttack(action, verbose)
	case lightClientLunaticAttackAction:
		tr.lightClientLunaticAttack(action, verbose)
	case registerRepresentativeAction:
		tr.registerRepresentative(action, verbose)
	case assignConsumerPubKeyAction:
		tr.assignConsumerPubKey(action, verbose)
	case slashThrottleDequeue:
		tr.waitForSlashThrottleDequeue(action, verbose)
	case startRelayerAction:
		tr.startRelayer(action, verbose)
	case submitChangeRewardDenomsProposalAction:
		tr.submitChangeRewardDenomsProposal(action, verbose)
	default:
		log.Fatalf("unknown action in testRun %s: %#v", tr.name, action)
	}

	modelState := step.State
	actualState := tr.getState(step.State)

	// Check state
	if !reflect.DeepEqual(actualState, modelState) {
		fmt.Printf("=============== %s FAILED ===============\n", tr.name)
		fmt.Println("FAILED action", reflect.TypeOf(step.Action).Name())
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
			tr.name, i+1, reflect.TypeOf(step.Action).Name())
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
		tr.containerConfig.ContainerName,
		tr.containerConfig.InstanceName,
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
	cmd := exec.Command("docker", "kill", tr.containerConfig.InstanceName)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}
