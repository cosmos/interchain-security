package main

import (
	"fmt"
	"os"
	"strconv"
	"time"
)

const (
	TEST_RESULT_PASS     = "PASSED"
	TEST_RESULT_FAIL     = "FAILED"
	TEST_RESULT_ERROR    = "ERROR"
	TEST_RESULT_SKIP     = "SKIP"
	TEST_STATUS_STARTED  = "STARTED"
	TEST_STATUS_FINISHED = "FINISHED"
	TEST_STATUS_NOTRUN   = "NO RUN"
)

var runnerId uint = 0

// A test runner drives the execution of test cases
// It sets up the test environment and the test driver to run the tests
type TestRunner struct {
	config     TestConfig
	stepChoice StepChoice
	testDriver TestCaseDriver
	target     ExecutionTarget
	verbose    bool
	result     TestResult
}

type TestResult struct {
	StartTime time.Time
	Status    string
	Duration  time.Duration
	Result    string
}

func (res *TestResult) Started() {
	if res.Status != "" {
		return
	}
	res.StartTime = time.Now()
	res.Status = TEST_STATUS_STARTED
}

func (res *TestResult) Failed() {
	if res.Result != "" {
		panic("Test result already set")
	}
	res.Duration = time.Since(res.StartTime)
	res.Result = TEST_RESULT_FAIL
	res.Status = TEST_STATUS_FINISHED
}

func (res *TestResult) Passed() {
	if res.Result != "" {
		panic("Test result already set")
	}
	res.Duration = time.Since(res.StartTime)
	res.Result = TEST_RESULT_PASS
	res.Status = TEST_STATUS_FINISHED
}

func (res *TestResult) Error() {
	if res.Result != "" {
		panic("Test result already set")
	}
	res.Duration = time.Since(res.StartTime)
	res.Result = TEST_RESULT_ERROR
	res.Status = TEST_STATUS_FINISHED
}

// Run will set up the test environment and executes the tests
func (tr *TestRunner) Run() error {
	tr.result = TestResult{}
	tr.result.Started()
	fmt.Printf("\n\n=============== running %s ===============\n", tr.stepChoice.name)
	fmt.Println(tr.Info())
	err := tr.checkConfig()
	if err != nil {
		return err
	}

	err = tr.setupEnvironment(tr.target)
	if err != nil {
		tr.result.Error()
		return fmt.Errorf("error setting up test environment: %v", err)
	}

	tr.testDriver = GetTestCaseDriver(tr.config)
	err = tr.testDriver.Run(tr.stepChoice.steps, tr.target, tr.verbose)
	if err != nil {
		tr.result.Failed()
		// not tearing down environment for troubleshooting reasons on container
		return fmt.Errorf("test run '%s' failed: %v", tr.config.Name, err)
	}

	tr.result.Passed()
	err = tr.teardownEnvironment()
	fmt.Printf("==========================================\n")
	return err
}

func (tr *TestRunner) checkConfig() error {
	tr.config.ValidateStringLiterals()
	return nil
}

func (tr *TestRunner) setupEnvironment(target ExecutionTarget) error {
	tr.target = target
	return target.Start()
}

func (tr *TestRunner) teardownEnvironment() error {
	if tr.skipCleanUp() {
		fmt.Println("Skip tear down !")
		return nil
	}
	return tr.target.Stop()
}

func (tr *TestRunner) skipCleanUp() bool {
	if value, present := os.LookupEnv("ICS_E2E_SKIP_CLEANUP"); present {
		if len(value) > 0 {
			if skipCleanup, err := strconv.ParseBool(value); err == nil {
				return skipCleanup
			}
		}
		return true
	}
	return false
}

func (tr *TestRunner) Setup(testCfg TestConfig) error {
	tr.config = testCfg
	return nil
}

func (tr *TestRunner) CleanUp() error {
	if tr.skipCleanUp() {
		return nil
	}
	return tr.target.Delete()
}

func CreateTestRunner(config TestConfig, stepChoice StepChoice, target ExecutionTarget, verbose bool) TestRunner {

	return TestRunner{
		target:     target,
		stepChoice: stepChoice,
		config:     config,
		verbose:    verbose,
		result:     TestResult{Status: TEST_STATUS_NOTRUN},
	}
}

// Info returns a header string containing useful information about the test runner
func (tr *TestRunner) Info() string {
	return fmt.Sprintf(`
-------------------------------------------------
Test name : %s
Config: %s
Target: %s
-------------------------------------------------`,
		tr.stepChoice.name,
		tr.config.Name,
		tr.target.Info(),
	)
}

func (tr *TestRunner) Report() string {
	return fmt.Sprintf(`
-------------------------------------------------
Test name : %s
Config: %s
Target: %s
- Status: %s
- Result: %s
- Duration: %s
- StartTime: %s
-------------------------------------------------`,
		tr.stepChoice.name,
		tr.config.Name,
		tr.target.Info(),
		tr.result.Status,
		tr.result.Result,
		tr.result.Duration,
		tr.result.StartTime,
	)
}
