package main

import (
	"fmt"
	"os"
	"os/exec"
)

type ModelConfig struct {
	modelPath string
	init      string
	step      string
}

type InvariantConfig struct {
	invariant  string
	numSamples int
	numSteps   int
}

// GenerateTraces generates a number of traces for a given invariant
// and stores them in a given folder.
// The traces will be named trace_0, trace_1, etc.
// For each trace that is produced, quint will run at most for numSteps steps,
// and run numSamples samples.
// If a quint run does not produce a trace that violates the invariant,
// it will not be retried, and there will simply be fewer than numTraces traces.
func GenerateTraces(numTraces int, modelConfig ModelConfig, invConfig InvariantConfig, traceFolder string) {
	// make sure the folder exists
	if err := os.MkdirAll(traceFolder, 0o755); err != nil {
		panic(err)
	}

	for i := 0; i < numTraces; i++ {
		// Generate trace
		traceName := fmt.Sprintf("trace_%d", i)
		GenerateTrace(modelConfig, invConfig, traceName)
	}
}

func GenerateTrace(modelConfig ModelConfig, invConfig InvariantConfig, traceName string) {
	cmd := fmt.Sprintf(
		"quint run --out-itf %v --init %v --step %v --invariant=%v --max-steps=%v --max-samples=%v %v",
		traceName,
		modelConfig.init,
		modelConfig.step,
		invConfig.invariant,
		invConfig.numSteps,
		invConfig.numSamples,
		modelConfig.modelPath,
	)

	fmt.Println(cmd)

	out, err := exec.Command("bash", "-c", cmd).CombinedOutput()
	if err != nil {
		fmt.Println(string(out))
		panic(err)
	}
}
