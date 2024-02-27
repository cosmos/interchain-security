package main

import (
	"fmt"
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

// A test runner drives the execution of test cases
// It sets up the test environment and the test driver to run the tests
type TestRunner struct {
	config     TestConfig
	steps      []Step
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

func (result *TestResult) Started() {
	result.StartTime = time.Now()
	result.Status = TEST_STATUS_STARTED
}

func (res *TestResult) Failed() {
	res.Duration = time.Since(res.StartTime)
	res.Result = TEST_RESULT_FAIL
	res.Status = TEST_STATUS_FINISHED
}

func (res *TestResult) Passed() {
	res.Duration = time.Since(res.StartTime)
	res.Result = TEST_RESULT_PASS
	res.Status = TEST_STATUS_FINISHED
}

func (res *TestResult) Error() {
	res.Duration = time.Since(res.StartTime)
	res.Result = TEST_RESULT_ERROR
	res.Status = TEST_STATUS_FINISHED
}

// Run will set up the test environment and executes the tests
func (tr *TestRunner) Run() error {
	tr.result = TestResult{}
	tr.result.Started()
	fmt.Printf("\n\n=============== running %s ===============\n", tr.config.name)
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
	err = tr.testDriver.Run(tr.steps, tr.target, tr.verbose)
	if err != nil {
		tr.result.Failed()
		// not tearing down environment for troubleshooting reasons on container
		return fmt.Errorf("test run '%s' failed: %v", tr.config.name, err)
	}

	tr.result.Passed()
	err = tr.teardownEnvironment()
	fmt.Printf("==========================================\n")
	return err
}

func (tr *TestRunner) checkConfig() error {
	tr.config.validateStringLiterals()
	return nil
}
func (tr *TestRunner) setupEnvironment(target ExecutionTarget) error {
	tr.target = target
	return target.Start()
}

func (tr *TestRunner) teardownEnvironment() error {
	return tr.target.Stop()
}

func (tr *TestRunner) Setup(testCfg TestConfig) error {
	tr.config = testCfg
	return nil
}

func CreateTestRunner(config TestConfig, steps []Step, target ExecutionTarget, verbose bool) (error, TestRunner) {
	//targetConfig := target.GetTargetConfig()
	switch target.(type) {
	case *DockerContainer:
		target.(*DockerContainer).containerCfg = config.containerConfig
	}
	tr := TestRunner{
		target:  target,
		steps:   steps,
		config:  config,
		verbose: verbose,
		result:  TestResult{Status: TEST_STATUS_NOTRUN},
	}
	return nil, tr
}

// Info returns a header string containing useful information about the test runner
func (tr *TestRunner) Info() string {
	return fmt.Sprintf(`
------------------------------------------
Test name : %s
Target: %s
------------------------------------------`,
		tr.config.name,
		tr.target.Info(),
	)

}

func (tr *TestRunner) Report() string {
	return fmt.Sprintf(`
------------------------------------------
Test name : %s
Target: %s
- Status: %s
- Result: %s
- Duration: %s
- StartTime: %s
------------------------------------------`,
		tr.config.name,
		tr.target.Info(),
		tr.result.Status,
		tr.result.Result,
		tr.result.Duration,
		tr.result.StartTime,
	)
}
