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
	for k := range *vs {
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
	testConfigs = map[string]TestConfigType{
		"default":                  DefaultTestCfg,
		"changeover":               ChangeoverTestCfg,
		"democracy":                DemocracyTestCfg,
		"democracy-reward":         DemocracyRewardTestCfg,
		"slash-throttle":           SlashThrottleTestCfg,
		"multiconsumer":            MulticonsumerTestCfg,
		"consumer-misbehaviour":    ConsumerMisbehaviourTestCfg,
		"consumer-double-sign":     DefaultTestCfg,
		"consumer-double-downtime": DefaultTestCfg,
	}
)

var selectedTestfiles TestSet

var stepChoices = map[string]StepChoice{
	"happy-path-short": {
		name:        "happy-path-short",
		steps:       shortHappyPathSteps,
		description: `This is like the happy path, but skips steps that involve starting or stopping nodes for the same chain outside of the chain setup or teardown. This is suited for CometMock+Gorelayer testing`,
		testConfig:  DefaultTestCfg,
	},
	"light-client-attack": {
		name:        "light-client-attack",
		steps:       lightClientAttackSteps,
		description: `This is like the short happy path, but will slash validators for LightClientAttackEvidence instead of DuplicateVoteEvidence. This is suited for CometMock+Gorelayer testing, but currently does not work with CometBFT, since causing light client attacks is not implemented`,
		testConfig:  DefaultTestCfg,
	},
	"happy-path": {
		name:        "happy-path",
		steps:       happyPathSteps,
		description: "happy path tests",
		testConfig:  DefaultTestCfg,
	},
	"changeover": {
		name:        "changeover",
		steps:       changeoverSteps,
		description: "changeover tests",
		testConfig:  ChangeoverTestCfg,
	},
	"democracy-reward": {
		name:        "democracy-reward",
		steps:       democracyRegisteredDenomSteps,
		description: "democracy tests allowing rewards",
		testConfig:  DemocracyRewardTestCfg,
	},
	"democracy": {
		name:        "democracy",
		steps:       democracyUnregisteredDenomSteps,
		description: "democracy tests",
		testConfig:  DemocracyTestCfg,
	},
	"slash-throttle": {
		name:        "slash-throttle",
		steps:       slashThrottleSteps,
		description: "slash throttle tests",
		testConfig:  SlashThrottleTestCfg,
	},
	"multiconsumer": {
		name:        "multiconsumer",
		steps:       multipleConsumers,
		description: "multi consumer tests",
		testConfig:  MulticonsumerTestCfg,
	},
	"consumer-misbehaviour": {
		name:        "consumer-misbehaviour",
		steps:       consumerMisbehaviourSteps,
		description: "consumer light client misbehaviour tests",
		testConfig:  ConsumerMisbehaviourTestCfg,
	},
	"consumer-double-sign": {
		name:        "consumer-double-sign",
		steps:       consumerDoubleSignSteps,
		description: "consumer double signing tests",
		testConfig:  DefaultTestCfg,
	},
	"consumer-double-downtime": {
		name:        "consumer-double-downtime",
		steps:       consumerDoubleDowntimeSteps,
		description: "jail a validator for two (different) downtime infractions on consumer",
		testConfig:  DefaultTestCfg,
	},
	"compatibility": {
		name:        "compatibility",
		steps:       compatibilitySteps,
		description: `Minimal set of test steps to perform compatibility tests`,
		testConfig:  CompatibilityTestCfg,
	},
	"partial-set-security-opt-in": {
		name:        "partial-set-security-opt-in",
		steps:       stepsOptInChain(),
		description: "test partial set security for an Opt-In chain",
		testConfig:  DefaultTestCfg,
	},
	"partial-set-security-top-n": {
		name:        "partial-set-security-top-n",
		steps:       stepsTopNChain(),
		description: "test partial set security for a Top-N chain",
		testConfig:  DefaultTestCfg,
	},
	"partial-set-security-validator-set-cap": {
		name:        "partial-set-security-validator-set-cap",
		steps:       stepsValidatorSetCappedChain(),
		description: "test partial set security for an Opt-In chain that is validator-set capped",
		testConfig:  DefaultTestCfg,
	},
	"partial-set-security-validators-power-cap": {
		name:        "partial-set-security-validators-power-cap",
		steps:       stepsValidatorsPowerCappedChain(),
		description: "test partial set security for an Opt-In chain that has its validators' power capped",
		testConfig:  DefaultTestCfg,
	},
	"partial-set-security-validators-allowlisted": {
		name:        "partial-set-security-validators-allowlisted",
		steps:       stepsValidatorsAllowlistedChain(),
		description: "test partial set security for an Opt-In chain that has some validators allowlisted",
		testConfig:  DefaultTestCfg,
	},
	"partial-set-security-validators-denylisted": {
		name:        "partial-set-security-validators-denylisted",
		steps:       stepsValidatorsDenylistedChain(),
		description: "test partial set security for an Opt-In chain that has a validator denylisted",
		testConfig:  DefaultTestCfg,
	},
	"partial-set-security-modification-proposal": {
		name:        "partial-set-security-modification-proposal",
		steps:       stepsModifyChain(),
		description: "test partial set security parameters can be changed through a modification proposal",
		testConfig:  DefaultTestCfg,
	},
	"active-set-changes": {
		name:        "active-set-changes",
		steps:       stepsActiveSetChanges(),
		description: "This is a regression test related to the issue discussed here: https://forum.cosmos.network/t/cosmos-hub-v17-1-chain-halt-post-mortem/13899. The test ensures that the protocol works as expected when MaxValidators is smaller than the number of potential validators.",
		testConfig:  SmallMaxValidatorsTestCfg,
	},
	"inactive-provider-validators-on-consumer": {
		name:        "inactive-provider-validators-on-consumer",
		steps:       stepsInactiveProviderValidators(),
		description: "test inactive validators on consumer",
		testConfig:  InactiveProviderValsTestCfg,
	},
	"inactive-vals-topN": {
		name:        "inactive-vals-topN",
		steps:       stepsInactiveValsWithTopN(),
		description: "test inactive validators on topN chain",
		testConfig:  InactiveProviderValsTestCfg,
	},
	"inactive-provider-validators-governance": {
		name:        "inactive-provider-validators-governance",
		steps:       stepsInactiveProviderValidatorsGovernance(),
		description: "test governance with inactive validators",
		testConfig:  InactiveValsGovTestCfg,
	},
	"inactive-provider-validators-governance-basecase": {
		name:        "inactive-provider-validators-governance-basecase",
		steps:       stepsInactiveProviderValidatorsGovernanceBasecase(),
		description: "comparison for governance when there are *no* inactive validators, to verify the difference to the governance test *with* inactive validators",
		testConfig:  GovTestCfg,
	},
	"min-stake": {
		name:        "min-stake",
		steps:       stepsMinStake(),
		description: "checks that the min stake parameter for consumer chains is respected",
		testConfig:  GovTestCfg, // see above: we reuse the GovTestCfg for convenience
	},
	"inactive-vals-mint": {
		name:        "inactive-vals-mint",
		steps:       stepsInactiveValsMint(),
		description: "test minting with inactive validators",
		testConfig:  InactiveValsMintTestCfg,
	},
	"mint-basecase": {
		name:        "mint-basecase",
		steps:       stepsMintBasecase(),
		description: "test minting without inactive validators as a sanity check",
		testConfig:  MintTestCfg,
	},
	"inactive-vals-outside-max-validators": {
		name:        "inactive-vals-outside-max-validators",
		steps:       stepsInactiveValsTopNReproduce(),
		description: "tests the behaviour of inactive validators with a top N = 100 chain and when max_validators is smaller than the total number of validators",
		testConfig:  InactiveValsExtraValsTestCfg,
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
		builder.WriteString(fmt.Sprintf("- %s\n", testConfig))
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
	testConfigSet := map[TestConfigType]struct{}{}
	for _, testConfig := range testConfigs {
		if _, ok := testConfigSet[testConfig]; !ok {
			builder.WriteString(fmt.Sprintf("- %s\n", testConfig))
			testConfigSet[testConfig] = struct{}{}
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
	config TestConfigType
	steps  StepChoice
}

func getTestCases(selectedPredefinedTests, selectedTestFiles TestSet, providerVersions,
	consumerVersions VersionSet,
) (tests []testStepsWithConfig) {
	// Run default tests if no test cases were selected
	if len(selectedPredefinedTests) == 0 && len(selectedTestFiles) == 0 {
		selectedPredefinedTests = TestSet{
			"changeover",
			"happy-path",
			"democracy-reward",
			"democracy",
			"slash-throttle",
			"consumer-double-sign",
			"consumer-misbehaviour",
			"consumer-double-downtime",
			"partial-set-security-opt-in",
			"partial-set-security-top-n",
			"partial-set-security-validator-set-cap",
			"partial-set-security-validators-power-cap",
			"partial-set-security-validators-allowlisted",
			"partial-set-security-validators-denylisted",
			"partial-set-security-modification-proposal",
			"active-set-changes",
			"inactive-provider-validators-on-consumer",
			"inactive-vals-topN",
			"inactive-provider-validators-governance",
			"min-stake",
			"inactive-vals-mint",
		}
		if includeMultiConsumer != nil && *includeMultiConsumer {
			selectedPredefinedTests = append(selectedPredefinedTests, "multiconsumer")
		}
	}

	tests = []testStepsWithConfig{}
	// Get predefined from selection
	for _, tc := range selectedPredefinedTests {
		testConfig := TestConfigType("")

		// first part of tc is the steps, second part is the test config
		splitTcString := strings.Split(tc, "::")
		if len(splitTcString) == 2 {
			tc = splitTcString[0]
			testConfig = TestConfigType(splitTcString[1])
		}

		if _, exists := stepChoices[tc]; !exists {
			log.Fatalf("Step choice '%s' not found.\nsee usage info:\n%s", tc, getTestCaseUsageString())
		}

		if testConfig == "" {
			testConfig = stepChoices[tc].testConfig
		}
		tests = append(tests, testStepsWithConfig{
			config: testConfig,
			steps:  stepChoices[tc],
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
			config: testConfig,
			steps: StepChoice{
				name:        testFileName,
				steps:       testCase,
				description: fmt.Sprintf("Steps from file %s", testFileName),
			},
		})
	}

	return tests
}

// delete all test targets
func deleteTargets(runners []TestRunner) {
	for _, runner := range runners {
		if err := runner.target.Delete(); err != nil {
			log.Println("error deleting target: ", err)
		}
	}
}

func createTestConfigs(cfgType TestConfigType, providerVersions, consumerVersions VersionSet) []TestConfig {
	var configs []TestConfig

	if len(consumerVersions) == 0 {
		consumerVersions[""] = true
	}
	if len(providerVersions) == 0 {
		providerVersions[""] = true
	}

	// Create test configs as a combination of "provider versions" with "consumer version" and "test case"
	for provider := range providerVersions {
		for consumer := range consumerVersions {
			// Skip target creation for same version of provider and consumer
			// if multiple versions need to be tested.
			// This is to reduce the tests to be run for compatibility testing.
			if (len(consumerVersions) > 1 || len(providerVersions) > 1) && consumer == provider {
				continue
			}
			config := GetTestConfig(cfgType, provider, consumer)
			config.SetRelayerConfig(*useGorelayer)
			config.SetCometMockConfig(*useCometmock)
			config.transformGenesis = *transformGenesis
			config.useGorelayer = *useGorelayer
			configs = append(configs, config)
		}
	}
	return configs
}

// createTestRunners creates test runners to run each test case on each target
func createTestRunners(testCases []testStepsWithConfig) []TestRunner {
	runners := []TestRunner{}
	targetCfg := TargetConfig{useGaia: *useGaia, localSdkPath: *localSdkPath, gaiaTag: *gaiaTag}

	for _, tc := range testCases {
		testConfigs := createTestConfigs(tc.config, providerVersions, consumerVersions)
		for _, cfg := range testConfigs {
			target, err := createTarget(cfg, targetCfg)
			tr := CreateTestRunner(cfg, tc.steps, &target, *verbose)
			if err == nil {
				fmt.Println("Created test runner for ", cfg.name,
					"with provVers=", cfg.providerVersion, "consVers=", cfg.consumerVersion)
				runners = append(runners, tr)
			} else {
				fmt.Println("No test runner created:", err)
			}
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

	for idx := range runners {
		if parallel != nil && *parallel {
			wg.Add(1)
			go func(runner *TestRunner) {
				defer wg.Done()
				result := runner.Run()
				if result != nil {
					log.Printf("Test '%s' failed", runner.config.name)
					err = result
				}
			}(&runners[idx])
		} else {
			rc := runners[idx].Run()
			if rc != nil {
				err = rc
			}
		}
	}

	if parallel != nil && *parallel {
		wg.Wait()
	}

	return err
}

func printReport(runners []TestRunner, duration time.Duration) {
	failedTests := []TestRunner{}
	passedTests := []TestRunner{}
	remainingTests := []TestRunner{}
	for _, t := range runners {
		switch t.result.Result {
		case TEST_RESULT_PASS:
			passedTests = append(passedTests, t)
		case TEST_RESULT_FAIL:
			failedTests = append(failedTests, t)
		default:
			remainingTests = append(remainingTests, t)
		}
	}
	numTotalTests := len(runners)
	report := `
=================================================
TEST RESULTS
-------------------------------------------------

`
	if len(failedTests) > 0 {
		report += fmt.Sprintln("\nFAILED TESTS:")
		for _, t := range failedTests {
			report += t.Report()
		}
	}
	if len(passedTests) > 0 {
		report += fmt.Sprintln("\n\nPASSED TESTS:")
		for _, t := range passedTests {
			report += t.Report()
		}
	}
	if len(remainingTests) > 0 {
		report += fmt.Sprintln("\n\nREMAINING TESTS:")
		for _, t := range remainingTests {
			report += t.Report()
		}
	}
	report += fmt.Sprintf(`
-------------------------------------------------
Summary:
- time elapsed: %s
- %d/%d tests passed
- %d/%d tests failed
- %d/%d tests with misc status (check details)
`,
		duration,
		len(passedTests), numTotalTests,
		len(failedTests), numTotalTests,
		len(remainingTests), numTotalTests,
	)

	report += fmt.Sprintln("\nFAILED TESTS:")
	for _, t := range failedTests {
		report += t.Report()
	}
	report += fmt.Sprintln("\n\nPASSED TESTS:")
	for _, t := range passedTests {
		report += t.Report()
	}

	report += fmt.Sprintln("\n\nREMAINING TESTS:")
	for _, t := range remainingTests {
		report += t.Report()
	}
	report += "=================================================="
	fmt.Print(report)
}

// runs E2E tests
// all docker containers are built sequentially to avoid race conditions when using local cosmos-sdk
// after building docker containers, all tests are run in parallel using their respective docker containers
func main() {
	if err := parseArguments(); err != nil {
		flag.Usage()
		log.Fatalf("Error parsing command arguments %s\n", err)
	}

	testCases := getTestCases(selectedTests, selectedTestfiles, providerVersions, consumerVersions)
	testRunners := createTestRunners(testCases)
	defer deleteTargets(testRunners)

	start := time.Now()
	err := executeTests(testRunners)
	if err != nil {
		log.Panicf("Test execution failed '%s'", err)
	}

	printReport(testRunners, time.Since(start))
}

type StepChoice struct {
	name        string
	steps       []Step
	description string
	testConfig  TestConfigType
}
