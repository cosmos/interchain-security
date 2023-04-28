package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
)

// TraceParser provides an interface for parsers that read sequences of Steps from files.
type TraceParser interface {
	ReadTraceFromFile(path string) []Step
}

// JSONParser is a simple parser that reads steps by unmarshalling from a file.
type JSONParser struct{}

func (parser JSONParser) ReadTraceFromFile(path string) ([]Step, error) {
	// Open the JSON file and read into a bite array
	jsonData, err := os.ReadFile(filepath.Clean(path))
	if err != nil {
		return nil, err
	}

	// Unmarshal the JSON into a slice of Step structs
<<<<<<< HEAD:tests/e2e/trace_parser.go
	var stepsWithActionTypes []StepWithActionType

	decoder := json.NewDecoder(bytes.NewReader(jsonData))
	decoder.DisallowUnknownFields() // To avoid silent errors. Will cause an error if the JSON contains unknown fields
	err = decoder.Decode(&stepsWithActionTypes)
=======
	var steps []Step
	err = json.Unmarshal(jsonData, &steps)
>>>>>>> 24b0ef1b (fix: e2e trace format fails on slashthrottlesteps (#903)):tests/e2e/json_parser.go
	if err != nil {
		return nil, err
	}

	return steps, nil
}
