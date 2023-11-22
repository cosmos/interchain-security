package main

import (
	"fmt"
	"log"
	"os"
	"os/exec"
	"strings"
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
// the trace will still be stored in the folder.
func GenerateTraces(numTraces int, modelConfig ModelConfig, invConfig InvariantConfig, traceFolder string) {
	// make sure the folder exists
	if err := os.MkdirAll(traceFolder, 0o755); err != nil {
		panic(err)
	}

	for i := 0; i < numTraces; i++ {
		// Generate trace
		traceName := fmt.Sprintf("%v/trace_%d", traceFolder, i)
		GenerateTrace(modelConfig, invConfig, traceName)

		log.Println("Generated trace", traceName)
	}
}

func GenerateTrace(modelConfig ModelConfig, invConfig InvariantConfig, traceName string) {
	var invariant_config string
	if invConfig.invariant != "" {
		invariant_config = fmt.Sprintf("--invariant=%v", invConfig.invariant)
	} else {
		invariant_config = ""
	}
	cmd := fmt.Sprintf(
		"quint run --out-itf %v --init %v --step %v %v --max-steps=%v --max-samples=%v %v",
		traceName,
		modelConfig.init,
		modelConfig.step,
		invariant_config,
		invConfig.numSteps,
		invConfig.numSamples,
		modelConfig.modelPath,
	)

	fmt.Println(cmd)

	out, err := exec.Command("bash", "-c", cmd).CombinedOutput()
	if err != nil {
		if strings.Contains(string(out), "Invariant violated") {
			return // this is an expected error, so no need to panic
		}
		fmt.Println(string(out))
		panic(err)
	}
}
