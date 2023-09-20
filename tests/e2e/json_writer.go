package main

import (
	"encoding/json"
	"os"
)

// TraceWriter is an interface for writers that write steps to files.
type TraceWriter interface {
	// WriteTraceToFile writes a given trace to a file, overwriting the file if it already exists.
	WriteTraceToFile(filepath string, trace []Step) error
}

// JSONWriter is a simple writer that marshals the array of Step objects.
// To identify which type of action is being used, we add a field to the Step struct.
type JSONWriter struct{}

var GlobalJSONWriter = JSONWriter{}

func (writer JSONWriter) WriteTraceToFile(filepath string, trace []Step) error {
	jsonobj, err := json.Marshal(trace)
	if err != nil {
		panic(err)
	}

	err = os.WriteFile(filepath, jsonobj, 0o600)
	return err
}
