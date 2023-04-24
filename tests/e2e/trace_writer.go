package main

import (
	"encoding/json"
	"fmt"
	"os"
)

// TraceWriter is an interface for writers that write steps to files.
type TraceWriter interface {
	WriteTraceToFile(filepath string, trace []Step)
}

// JSONWriter is a simple writer that simply marshals the array of Step objects
type JSONWriter struct{}

func (writer JSONWriter) WriteTraceToFile(filepath string, trace []Step) error {
	jsonobj, err := json.Marshal(trace)
	if err != nil {
		return err
	}

	// for debugging:
	fmt.Println(string(jsonobj))

	err = os.WriteFile(filepath, jsonobj, 0o644)
	return err
}
