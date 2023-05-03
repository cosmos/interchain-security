package main

import (
	"log"
	"os"
	"path/filepath"
	"testing"

	"pgregory.net/rapid"
)

func TestReadAndWriteTrace(t *testing.T) {
	parser := JSONParser{}
	writer := JSONWriter{}

	dir, err := os.MkdirTemp("", "example")
	if err != nil {
		log.Fatal(err)
	}
	defer os.RemoveAll(dir) // clean up

	rapid.Check(t, func(t *rapid.T) {
		trace := GetTraceGen().Draw(t, "Trace")
		filename := filepath.Join(dir, "trace.json")
		err := WriteAndReadTrace(parser, writer, trace, filename)
		if err != nil {
			t.Fatalf("error writing and reading trace: %v", err)
		}
	})
}

func GetTraceGen() *rapid.Generator[[]Step] {
	return rapid.SliceOf(GetStepGen())
}

func GetStepGen() *rapid.Generator[Step] {
	return rapid.Custom(func(t *rapid.T) Step {
		return Step{
			Action: GetActionGen().Draw(t, "Action"),
			State:  GetStateGen().Draw(t, "State"),
		}
	})
}
