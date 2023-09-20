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
	testSelection TestSet
	testMap       map[string]*testRunWithSteps = map[string]*testRunWithSteps{
		"happy-path-short": {
			testRun: DefaultTestRun(), steps: shortHappyPathSteps,
			description: `This is like the happy path, but skips steps
that involve starting or stopping nodes for the same chain outside of the chain setup or teardown.
This is suited for CometMock+Gorelayer testing`,
		},
		"light-client-attack": {
			testRun: DefaultTestRun(), steps: lightClientAttackSteps,
			description: `This is like the short happy path, but will slash validators for LightClientAttackEvidence instead of DuplicateVoteEvidence.
This is suited for CometMock+Gorelayer testing, but currently does not work with CometBFT,
since causing light client attacks is not implemented.`,
		},
		"happy-path":       {testRun: DefaultTestRun(), steps: happyPathSteps, description: "happy path tests"},
		"changeover":       {testRun: ChangeoverTestRun(), steps: changeoverSteps, description: "changeover tests"},
		"democracy-reward": {testRun: DemocracyTestRun(true), steps: democracyRewardsSteps, description: "democracy tests allowing rewards"},
		"democracy":        {testRun: DemocracyTestRun(false), steps: democracySteps, description: "democracy tests"},
		"slash-throttle":   {testRun: SlashThrottleTestRun(), steps: slashThrottleSteps, description: "slash throttle tests"},
		"multiconsumer":    {testRun: MultiConsumerTestRun(), steps: multipleConsumers, description: "multi consumer tests"},
	}
)

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

func parseArguments() (err error) {
	flag.Var(&testSelection, "tc",
		fmt.Sprintf("Selection of test cases to be executed:\n%s,\n%s",
			func() string {
				var keys []string
				for k, v := range testMap {
					keys = append(keys, fmt.Sprintf("- %s : %s", k, v.description))
				}
				return strings.Join(keys, "\n")
			}(),
			"Example: -tc multiconsumer -tc happy-path "))
	flag.Parse()

	// Enforce go-relayer in case of cometmock as hermes is not yet supported
	if useCometmock != nil && *useCometmock && (useGorelayer == nil || !*useGorelayer) {
		fmt.Println("Enforcing go-relayer as cometmock is requested")
		if err = flag.Set("use-gorelayer", "true"); err != nil {
			return
		}
	}
	// check if specified test case exists
	for _, tc := range testSelection {
		if _, hasKey := testMap[tc]; !hasKey {
			err := fmt.Errorf("unknown test case '%s'", tc)
			return err
		}
	}
	return
}

func getTestCases(selection TestSet) (tests []testRunWithSteps) {
	// Run default tests if no test cases were selected
	if len(selection) == 0 {
		selection = TestSet{
			"changeover", "happy-path",
			"democracy-reward", "democracy", "slash-throttle",
		}
		if includeMultiConsumer != nil && *includeMultiConsumer {
			selection = append(selection, "multiconsumer")
		}
	}

	// Get tests from selection
	tests = []testRunWithSteps{}
	for _, tc := range selection {
		if _, exists := testMap[tc]; !exists {
			log.Fatalf("Test case '%s' not found", tc)
		}
		tests = append(tests, *testMap[tc])
	}
	return
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

type testRunWithSteps struct {
	testRun     TestRun
	steps       []Step
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
	case slashMeterReplenishmentAction:
		tr.waitForSlashMeterReplenishment(action, verbose)
	case waitTimeAction:
		tr.waitForTime(action, verbose)
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
