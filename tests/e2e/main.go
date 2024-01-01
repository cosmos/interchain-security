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
	selectedTests TestSet

	// map the test config names to their structs to allow for easy selection of test configs,
	// and also to programmatically set parameters, i.e. see DemocracyTestConfig
	testConfigs = map[string]TestConfig{
		"default":               DefaultTestConfig(),
		"changeover":            ChangeoverTestConfig(),
		"democracy":             DemocracyTestConfig(false),
		"democracy-reward":      DemocracyTestConfig(true),
		"slash-throttle":        SlashThrottleTestConfig(),
		"multiconsumer":         MultiConsumerTestConfig(),
		"consumer-misbehaviour": ConsumerMisbehaviourTestConfig(),
		"consumer-double-sign":  DefaultTestConfig(),
	}
)

var selectedTestfiles TestSet

var stepChoices = map[string]StepChoice{
	"happy-path-short": {
		name:        "happy-path-short",
		steps:       shortHappyPathSteps,
		description: `This is like the happy path, but skips steps that involve starting or stopping nodes for the same chain outside of the chain setup or teardown. This is suited for CometMock+Gorelayer testing`,
		testConfig:  DefaultTestConfig(),
	},
	"light-client-attack": {
		name:        "light-client-attack",
		steps:       lightClientAttackSteps,
		description: `This is like the short happy path, but will slash validators for LightClientAttackEvidence instead of DuplicateVoteEvidence. This is suited for CometMock+Gorelayer testing, but currently does not work with CometBFT, since causing light client attacks is not implemented`,
		testConfig:  DefaultTestConfig(),
	},
	"happy-path": {
		name:        "happy-path",
		steps:       happyPathSteps,
		description: "happy path tests",
		testConfig:  DefaultTestConfig(),
	},
	"changeover": {
		name:        "changeover",
		steps:       changeoverSteps,
		description: "changeover tests",
		testConfig:  ChangeoverTestConfig(),
	},
	"democracy-reward": {
		name:        "democracy-reward",
		steps:       democracyRewardsSteps,
		description: "democracy tests allowing rewards",
		testConfig:  DemocracyTestConfig(true),
	},
	"democracy": {
		name:        "democracy",
		steps:       democracySteps,
		description: "democracy tests",
		testConfig:  DemocracyTestConfig(false),
	},
	"slash-throttle": {
		name:        "slash-throttle",
		steps:       slashThrottleSteps,
		description: "slash throttle tests",
		testConfig:  SlashThrottleTestConfig(),
	},
	"multiconsumer": {
		name:        "multiconsumer",
		steps:       multipleConsumers,
		description: "multi consumer tests",
		testConfig:  MultiConsumerTestConfig(),
	},
	"consumer-misbehaviour": {
		name:        "consumer-misbehaviour",
		steps:       consumerMisbehaviourSteps,
		description: "consumer light client misbehaviour tests",
		testConfig:  ConsumerMisbehaviourTestConfig(),
	},
	"consumer-double-sign": {
		name:        "consumer-double-sign",
		steps:       consumerDoubleSignSteps,
		description: "consumer double signing tests",
		testConfig:  DefaultTestConfig(),
	},
}

func executeTests(tests []testStepsWithConfig) (err error) {
	if parallel != nil && *parallel {
		fmt.Println("=============== running all tests in parallel ===============")
	}

	var wg sync.WaitGroup
	for _, testCase := range tests {
		if parallel != nil && *parallel {
			wg.Add(1)
			go func(run testStepsWithConfig) {
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
	builder.WriteString("This flag is used to reference existing, defined test cases to be run.")
	builder.WriteString("Test case selection:\nSelection of test steps to be executed:\n")
	for _, stepChoice := range stepChoices {
		builder.WriteString(fmt.Sprintf("- %s : %s.\n", stepChoice.name, stepChoice.description))
	}
	builder.WriteString("\n")

	// Test runner selection
	builder.WriteString("Test runner selection:\nSelection of test runners to be executed:\n")
	for _, testConfig := range testConfigs {
		builder.WriteString(fmt.Sprintf("- %s\n", testConfig.name))
	}
	builder.WriteString("\n")

	// Example
	builder.WriteString("Example: -tc multiconsumer::multiconsumer -tc happy-path::default")

	return builder.String()
}

func getTestFileUsageString() string {
	var builder strings.Builder

	builder.WriteString("This flag is used to reference files containing step traces to be run.\n")
	builder.WriteString("Each filename should be separated by '::' from the test runner name.\n")

	// Test runner selection
	builder.WriteString("Test runner selection:\nSelection of test runners to be executed:\n")
	testConfigSet := map[string]struct{}{}
	for _, testConfig := range testConfigs {
		if _, ok := testConfigSet[testConfig.name]; !ok {
			builder.WriteString(fmt.Sprintf("- %s\n", testConfig.name))
			testConfigSet[testConfig.name] = struct{}{}
		}
	}
	builder.WriteString("\n")

	// Example
	builder.WriteString("Example: -test-file awesome-trace.json::default -test-file other-trace.json::default")

	return builder.String()
}

func parseArguments() (err error) {
	flag.Var(&selectedTests, "tc",
		getTestCaseUsageString())

	flag.Var(&selectedTestfiles, "test-file",
		getTestFileUsageString())
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

type testStepsWithConfig struct {
	testRun TestConfig
	steps   []Step
}

func getTestCases(selectedPredefinedTests, selectedTestFiles TestSet) (tests []testStepsWithConfig) {
	// Run default tests if no test cases were selected
	if len(selectedPredefinedTests) == 0 && len(selectedTestFiles) == 0 {
		selectedPredefinedTests = TestSet{
			"changeover", "happy-path",
			"democracy-reward", "democracy",
			"slash-throttle", "consumer-double-sign", "consumer-misbehaviour",
		}
		if includeMultiConsumer != nil && *includeMultiConsumer {
			selectedPredefinedTests = append(selectedPredefinedTests, "multiconsumer")
		}
	}

	tests = []testStepsWithConfig{}
	// Get predefined from selection
	for _, tc := range selectedPredefinedTests {
		// first part of tc is the steps, second part is the test runner

		if _, exists := stepChoices[tc]; !exists {
			log.Fatalf("Step choice '%s' not found.\nsee usage info:\n%s", tc, getTestCaseUsageString())
		}

		stepChoice := stepChoices[tc]

		tests = append(tests, testStepsWithConfig{
			testRun: stepChoice.testConfig,
			steps:   stepChoice.steps,
		},
		)
	}

	// get test cases from files
	for _, testFile := range selectedTestFiles {
		// first part is the file, second part is the test runner
		splitTcString := strings.Split(testFile, "::")
		if len(splitTcString) != 2 {
			log.Fatalf("Test file '%s' is invalid.\nsee usage info:\n%s", testFile, getTestFileUsageString())
		}

		testFileName := splitTcString[0]
		testRunnerName := splitTcString[1]

		if _, exists := testConfigs[testRunnerName]; !exists {
			log.Fatalf("Test runner '%s' not found.\nsee usage info:\n%s", testRunnerName, getTestFileUsageString())
		}

		testConfig := testConfigs[testRunnerName]

		testCase, err := GlobalJSONParser.ReadTraceFromFile(testFileName)
		if err != nil {
			log.Fatalf("Error reading test file '%s': %s", testFileName, err)
		}

		tests = append(tests, testStepsWithConfig{
			testRun: testConfig,
			steps:   testCase,
		})
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

	testCases := getTestCases(selectedTests, selectedTestfiles)

	start := time.Now()
	err := executeTests(testCases)
	if err != nil {
		log.Fatalf("Test execution failed '%s'", err)
	}
	log.Printf("TOTAL TIME ELAPSED: %v\n", time.Since(start))
}

// Run sets up docker container and executes the steps in the test run.
// Docker containers are torn down after the test run is complete.
func (tr *TestConfig) Run(steps []Step, localSdkPath string, useGaia bool, gaiaTag string) {
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
	testConfig  TestConfig
}

func (tr *TestConfig) runStep(step Step, verbose bool) {
	switch action := step.Action.(type) {
	case StartChainAction:
		tr.startChain(action, verbose)
	case StartSovereignChainAction:
		tr.startSovereignChain(action, verbose)
	case LegacyUpgradeProposalAction:
		tr.submitLegacyUpgradeProposal(action, verbose)
	case WaitUntilBlockAction:
		tr.waitUntilBlockOnChain(action)
	case ChangeoverChainAction:
		tr.changeoverChain(action, verbose)
	case SendTokensAction:
		tr.sendTokens(action, verbose)
	case SubmitTextProposalAction:
		tr.submitTextProposal(action, verbose)
	case SubmitConsumerAdditionProposalAction:
		tr.submitConsumerAdditionProposal(action, verbose)
	case SubmitConsumerRemovalProposalAction:
		tr.submitConsumerRemovalProposal(action, verbose)
	case SubmitParamChangeLegacyProposalAction:
		tr.submitParamChangeProposal(action, verbose)
	case VoteGovProposalAction:
		tr.voteGovProposal(action, verbose)
	case StartConsumerChainAction:
		tr.startConsumerChain(action, verbose)
	case AddChainToRelayerAction:
		tr.addChainToRelayer(action, verbose)
	case CreateIbcClientsAction:
		tr.createIbcClientsHermes(action, verbose)
	case AddIbcConnectionAction:
		tr.addIbcConnection(action, verbose)
	case AddIbcChannelAction:
		tr.addIbcChannel(action, verbose)
	case TransferChannelCompleteAction:
		tr.transferChannelComplete(action, verbose)
	case RelayPacketsAction:
		tr.relayPackets(action, verbose)
	case RelayRewardPacketsToProviderAction:
		tr.relayRewardPacketsToProvider(action, verbose)
	case DelegateTokensAction:
		tr.delegateTokens(action, verbose)
	case UnbondTokensAction:
		tr.unbondTokens(action, verbose)
	case CancelUnbondTokensAction:
		tr.cancelUnbondTokens(action, verbose)
	case RedelegateTokensAction:
		tr.redelegateTokens(action, verbose)
	case DowntimeSlashAction:
		tr.invokeDowntimeSlash(action, verbose)
	case UnjailValidatorAction:
		tr.unjailValidator(action, verbose)
	case DoublesignSlashAction:
		tr.invokeDoublesignSlash(action, verbose)
	case LightClientAmnesiaAttackAction:
		tr.lightClientAmnesiaAttack(action, verbose)
	case LightClientEquivocationAttackAction:
		tr.lightClientEquivocationAttack(action, verbose)
	case LightClientLunaticAttackAction:
		tr.lightClientLunaticAttack(action, verbose)
	case RegisterRepresentativeAction:
		tr.registerRepresentative(action, verbose)
	case AssignConsumerPubKeyAction:
		tr.assignConsumerPubKey(action, verbose)
	case SlashMeterReplenishmentAction:
		tr.waitForSlashMeterReplenishment(action, verbose)
	case WaitTimeAction:
		tr.waitForTime(action, verbose)
	case StartRelayerAction:
		tr.startRelayer(action, verbose)
	case ForkConsumerChainAction:
		tr.forkConsumerChain(action, verbose)
	case UpdateLightClientAction:
		tr.updateLightClient(action, verbose)
	case StartConsumerEvidenceDetectorAction:
		tr.startConsumerEvidenceDetector(action, verbose)
	case SubmitChangeRewardDenomsProposalAction:
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
func (tr *TestConfig) executeSteps(steps []Step) {
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

func (tr *TestConfig) startDocker() {
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
func (tr *TestConfig) teardownDocker() {
	fmt.Printf("===============  tearing down %s testRun ===============\n", tr.name)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "kill", tr.containerConfig.InstanceName)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}
