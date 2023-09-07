package main

import (
	"bytes"
	"encoding/json"
	"fmt"
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
	var stepsWithActionTypes []StepWithActionType

	decoder := json.NewDecoder(bytes.NewReader(jsonData))
	decoder.DisallowUnknownFields() // To avoid silent errors. Will cause an error if the JSON contains unknown fields
	err = decoder.Decode(&stepsWithActionTypes)
	if err != nil {
		return nil, err
	}

	steps := make([]Step, len(stepsWithActionTypes))

	// Unmarshal the actions inside the steps from map[string]any to the corresponding action type
	for i, step := range stepsWithActionTypes {
		action, err := UnmarshalMapToActionType(step.Action.(map[string]any), step.ActionType)
		if err != nil {
			return nil, err
		}

		fmt.Println(action)

		steps[i] = Step{action, step.State}

	}

	return steps, nil
}
