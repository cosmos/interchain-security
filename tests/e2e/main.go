package main

import (
	"flag"
	"fmt"
	"log"
	"strings"
	"sync"
	"time"
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

type VersionSet map[string]bool

func (vs *VersionSet) Set(value string) error {
	(*vs)[value] = true
	return nil
}

func (vs *VersionSet) String() string {
	keys := []string{}
	for k, _ := range *vs {
		keys = append(keys, k)
	}
	return fmt.Sprint(keys)
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
	consumerVersions VersionSet = VersionSet{}
	providerVersions VersionSet = VersionSet{}
	transformGenesis            = flag.Bool("transform-genesis", false, "enforces a consumer app to perform genesis transformation of exported ccv genesis data. For details see compatibility notes (RELEASES.md) of used versions")
)

var (
	selectedTests TestSet

	// map the test config names to their structs to allow for easy selection of test configs,
	// and also to programmatically set parameters, i.e. see DemocracyTestConfig
	testConfigs = map[string]TestConfig{
		"default":                  DefaultTestConfig(),
		"changeover":               ChangeoverTestConfig(),
		"democracy":                DemocracyTestConfig(false),
		"democracy-reward":         DemocracyTestConfig(true),
		"slash-throttle":           SlashThrottleTestConfig(),
		"multiconsumer":            MultiConsumerTestConfig(),
		"consumer-misbehaviour":    ConsumerMisbehaviourTestConfig(),
		"consumer-double-sign":     DefaultTestConfig(),
		"consumer-double-downtime": DefaultTestConfig(),
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
	"consumer-double-downtime": {
		name:        "consumer-double-downtime",
		steps:       consumerDoubleDowntimeSteps,
		description: "jail a validator for two (different) downtime infractions on consumer",
		testConfig:  DefaultTestConfig(),
	},
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

	flag.Var(&consumerVersions, "cv", "Version (git tag, revision, branch) of the consumer to be tested. Tests will be run against combinations of all defined provider versions (-pv) with this consumer version. Default: consumer implementation of local workspace")
	flag.Var(&providerVersions, "pv", "Version (git tag, revision, branch) of the provider to be tested. Tests will be run against combinations of all defined consumer versions (-cv) with this provider version. Default: provider implementation of local workspace")

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
			"consumer-double-downtime",
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

// delete all test targets
func deleteTargets(targets []ExecutionTarget) {
	for _, target := range targets {
		if err := target.Delete(); err != nil {
			log.Println("error deleting target: ", err)
		}
	}
}

// Create targets where test cases should be executed on
// For each combination of provider & consumer versions an ExecutionTarget
// is created.
func createTargets(providerVersions, consumerVersions VersionSet) ([]ExecutionTarget, error) {
	targetCfg := TargetConfig{useGaia: *useGaia, localSdkPath: *localSdkPath, gaiaTag: *gaiaTag}
	var targets []ExecutionTarget

	if len(consumerVersions) == 0 {
		consumerVersions[""] = true
	}
	if len(providerVersions) == 0 {
		providerVersions[""] = true
	}

	for provider, _ := range providerVersions {
		for consumer, _ := range consumerVersions {
			targetCfg.consumerVersion = consumer
			targetCfg.providerVersion = provider
			target := DockerContainer{targetConfig: targetCfg}
			err := target.Build()
			if err != nil {
				log.Println("@@@ failed creating target")
				deleteTargets(targets)
				return nil, err
			}
			targets = append(targets, &target)
		}
	}
	return targets, nil
}

func createTestRunners(targets []ExecutionTarget, testCases []testStepsWithConfig) []TestRunner {
	runners := []TestRunner{}
	for _, target := range targets {
		for _, tc := range testCases {
			tr := TestRunner{
				config:  tc.testRun,
				steps:   tc.steps,
				target:  target,
				verbose: *verbose,
			}
			//TODO: refactor this target specific setting
			tr.target.(*DockerContainer).containerCfg = tc.testRun.containerConfig
			tr.config.transformGenesis = *transformGenesis
			tr.config.SetCometMockConfig(*useCometmock)
			tr.config.SetRelayerConfig(*useGorelayer)
			runners = append(runners, tr)
		}
	}
	return runners
}

func executeTests(runners []TestRunner) error {
	if parallel != nil && *parallel {
		fmt.Println("=============== running all tests in parallel ===============")
	}

	var wg sync.WaitGroup
	var err error = nil

	for _, runner := range runners {
		if parallel != nil && *parallel {
			wg.Add(1)
			go func(runner TestRunner) {
				defer wg.Done()
				result := runner.Run()
				if result != nil {
					log.Printf("Test '%s' failed", runner.config.name)
					err = result
				}
			}(runner)
		} else {
			fmt.Printf("=============== running %s ===============\n", runner.config.name)
			err = runner.Run()
		}
	}

	if parallel != nil && *parallel {
		wg.Wait()
	}

	return err
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
	targets, err := createTargets(providerVersions, consumerVersions)
	if err != nil {
		log.Fatal("failed creating test targets: ", err)
	}
	defer func() { deleteTargets(targets) }()

	testRunners := createTestRunners(targets, testCases)
	start := time.Now()
	err = executeTests(testRunners)
	if err != nil {
		log.Fatalf("Test execution failed '%s'", err)
	}
	log.Printf("TOTAL TIME ELAPSED: %v\n", time.Since(start))

}

type StepChoice struct {
	name        string
	steps       []Step
	description string
	testConfig  TestConfig
}
