package main

import (
	"encoding/json"
	"os"
	"path/filepath"
)

// TraceParser provides an interface for parsers that read sequences of Steps from files.
type TraceParser interface {
	ReadTraceFromFile(filepath string) ([]Step, error)
}

// JSONParser is a simple parser that reads steps by unmarshalling from a file.
type JSONParser struct{}

var GlobalJSONParser = JSONParser{}

func (parser JSONParser) ReadTraceFromFile(path string) ([]Step, error) {
	// Open the JSON file and read into a byte array
	jsonData, err := os.ReadFile(filepath.Clean(path))
	if err != nil {
		return nil, err
	}

	// Unmarshal the JSON into a slice of Step structs
	var steps []Step

	err = json.Unmarshal(jsonData, &steps)
	if err != nil {
		return nil, err
	}

	return steps, nil
}
