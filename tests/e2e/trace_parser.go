package main

import (
	"encoding/json"
	"io/ioutil"
	"os"
)

// TraceParser provides an interface for parsers that read sequences of Steps from files.
type TraceParser interface {
	ReadTraceFromFile(filepath string) []Step
}

// JSONParser is a simple parser that reads steps by unmarshalling from a file.
type JSONParser struct{}

func (parser JSONParser) ReadTraceFromFile(filepath string) ([]Step, error) {
	// Open the JSON file
	jsonFile, err := os.Open(filepath)
	if err != nil {
		return nil, err
	}
	defer jsonFile.Close()

	// Read the file into a byte array
	jsonData, err := ioutil.ReadAll(jsonFile)
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
