package main

import "fmt"

// A test runner drives the execution of test cases
// It sets up the test environment and the test driver to run the tests
type TestRunner struct {
	config     TestConfig
	steps      []Step
	testDriver TestCaseDriver
	target     ExecutionTarget
	verbose    bool
}

// Run will set up the test environment and executes the tests
func (tr *TestRunner) Run() error {
	fmt.Printf("=============== running %s ===============\n", tr.config.name)
	fmt.Println(tr.Info())
	err := tr.checkConfig()
	if err != nil {
		return err
	}

	err = tr.setupEnvironment(tr.target)
	if err != nil {
		return fmt.Errorf("error setting up test environment: %v", err)
	}

	tr.testDriver = GetTestCaseDriver(tr.config)
	err = tr.testDriver.Run(tr.steps, tr.target, tr.verbose)
	if err != nil {
		// not tearing down environment for troubleshooting reasons on container
		return fmt.Errorf("test run '%s' failed: %v", tr.config.name, err)
	}
	return tr.teardownEnvironment()
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
	}
	return nil, tr
}

// Info returns a header string containing useful information about the test runner
func (tr *TestRunner) Info() string {
	return fmt.Sprintf(`
------------------------------------------
Test name : %s
Target:
%s
------------------------------------------`,
		tr.config.name,
		tr.target.Info(),
	)

}
