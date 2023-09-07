package main

import (
	"encoding/json"
	"fmt"
	"os"
	"reflect"
	"strings"
)

// TraceWriter is an interface for writers that write steps to files.
type TraceWriter interface {
	WriteTraceToFile(filepath string, trace []Step)
}

// JSONWriter is a simple writer that simply marshals the array of Step objects.
// To identify which type of action is being used, we add a field to the Step struct.
type JSONWriter struct{}

func (writer JSONWriter) WriteTraceToFile(filepath string, trace []Step) error {
	// collect missing action types, if any. this way, we can provide a more helpful error message.

	// workaround: we would keep a set, but go doesn't have sets.
	missingActionTypes := make(map[string]struct{}, 0)

	traceWithMarshalledActions := make([]StepWithActionType, 0)
	for _, step := range trace {
		actionType := reflect.TypeOf(step.Action).String()
		_, ok := actionRegistry[actionType]
		if !ok {
			missingActionTypes[actionType] = struct{}{}
		}
		traceWithMarshalledActions = append(traceWithMarshalledActions, StepWithActionType{step, actionType})
	}
	if len(missingActionTypes) > 0 {
		missingActionTypesString := ""
		for actionType := range missingActionTypes {
			// the actionType might start with module names, which we need to strip
			strippedActionType := actionType[strings.LastIndex(actionType, ".")+1:]
			missingActionTypesString += fmt.Sprintf("\"%v\": reflect.TypeOf(%v{}),", actionType, strippedActionType)
			missingActionTypesString += "\n"
		}
		return fmt.Errorf("missing some action types!\n you probably want to add the following lines\n"+
			"to the action registry in interchain-security/tests/e2e/trace_utils.go:\n%v", missingActionTypesString)
	}
	jsonobj, err := json.Marshal(traceWithMarshalledActions)
	if err != nil {
		panic(err)
	}

	err = os.WriteFile(filepath, jsonobj, 0o600)
	return err
}
