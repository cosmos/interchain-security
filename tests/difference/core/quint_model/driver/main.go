package main

import (
	"flag"
	"fmt"
	"os"
)

// main generates traces according to a given config
// and stores them in a folder.
// This can be used to generate traces for testing, see mbt_test.go
func main() {
	// Define command-line flags
	modelPath := flag.String("modelPath", "", "Path to the model")
	init := flag.String("init", "init", "init action to use for quint")
	step := flag.String("step", "step", "step action to use for quint")
	invariant := flag.String("invariant", "", "The invariant to check")
	numSamples := flag.Int("numSamples", 20, "Number of samples")
	numSteps := flag.Int("numSteps", 20, "Number of steps")
	traceFolder := flag.String("traceFolder", "", "Path to the trace folder")
	numTraces := flag.Int("numTraces", 0, "Number of traces to generate")

	// Parse command-line flags
	flag.Parse()

	// ensure flags were set
	if *modelPath == "" {
		fmt.Println("Error: modelPath flag is required")
		os.Exit(1)
	}

	if *traceFolder == "" {
		fmt.Println("Error: traceFolder flag is required")
		os.Exit(1)
	}

	if *numTraces == 0 {
		fmt.Println("Error: numTraces flag is required")
		os.Exit(1)
	}

	// Create ModelConfig and InvariantConfig instances
	modelConfig := ModelConfig{
		modelPath: *modelPath,
		init:      *init,
		step:      *step,
	}

	invariantConfig := InvariantConfig{
		invariant:  *invariant,
		numSamples: *numSamples,
		numSteps:   *numSteps,
	}

	// Print the parsed values
	fmt.Println("Model Config:")
	fmt.Println("Model Path:", modelConfig.modelPath)
	fmt.Println("Init:", modelConfig.init)
	fmt.Println("Step:", modelConfig.step)

	fmt.Println("Invariant Config:")
	fmt.Println("Invariant:", invariantConfig.invariant)
	fmt.Println("Num Samples:", invariantConfig.numSamples)
	fmt.Println("Num Steps:", invariantConfig.numSteps)

	fmt.Println("Trace Folder:", *traceFolder)

	fmt.Println("Num Traces:", *numTraces)

	// Generate the traces
	GenerateTraces(*numTraces, modelConfig, invariantConfig, *traceFolder)
}
