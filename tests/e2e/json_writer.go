package main

import (
	"encoding/json"
	"os"
)

// TraceWriter is an interface for writers that write steps to files.
type TraceWriter interface {
	WriteTraceToFile(filepath string, trace []Step) error
}

// JSONWriter is a simple writer that marshals the array of Step objects.
// To identify which type of action is being used, we add a field to the Step struct.
type JSONWriter struct{}

var GlobalJSONWriter = JSONWriter{}

func (writer JSONWriter) WriteTraceToFile(filepath string, trace []Step) error {
	// collect missing action types, if any. this way, we can provide a more helpful error message.

	// workaround: we would keep a set, but go doesn't have sets.
	jsonobj, err := json.Marshal(trace)
	if err != nil {
		panic(err)
	}

	err = os.WriteFile(filepath, jsonobj, 0o600)
	return err
}
