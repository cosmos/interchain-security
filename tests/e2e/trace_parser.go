package main

import (
	"encoding/json"
	"fmt"
	"os"
)

// TraceParser provides an interface for parsers that read sequences of Steps from files.
type TraceParser interface {
	ReadTraceFromFile(filepath string) []Step
}

// JSONParser is a simple parser that reads steps by unmarshalling from a file.
type JSONParser struct{}

func (parser JSONParser) ReadTraceFromFile(filepath string) ([]Step, error) {
	// Open the JSON file and read into a bite array
	jsonData, err := os.ReadFile(filepath)
	if err != nil {
		return nil, err
	}

	// Unmarshal the JSON into a slice of Step structs
	var stepsWithActionTypes []StepWithActionType
	err = json.Unmarshal(jsonData, &stepsWithActionTypes)
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
