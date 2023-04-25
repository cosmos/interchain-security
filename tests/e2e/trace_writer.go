package main

import (
	"encoding/json"
	"os"
	"reflect"
)

// TraceWriter is an interface for writers that write steps to files.
type TraceWriter interface {
	WriteTraceToFile(filepath string, trace []Step)
}

// JSONWriter is a simple writer that simply marshals the array of Step objects.
// To identify which type of action is being used, we add a field to the Step struct.
type JSONWriter struct{}

func (writer JSONWriter) WriteTraceToFile(filepath string, trace []Step) error {
	traceWithMarshalledActions := make([]StepWithActionType, 0)
	for _, step := range trace {
		actionType := reflect.TypeOf(step.Action).String()
		traceWithMarshalledActions = append(traceWithMarshalledActions, StepWithActionType{step, actionType})
	}
	jsonobj, err := json.Marshal(traceWithMarshalledActions)
	if err != nil {
		return err
	}

	err = os.WriteFile(filepath, jsonobj, 0o600)
	return err
}
