package main

import (
	"testing"

	"github.com/google/go-cmp/cmp"
)

func CheckErrorMatchesExpectation(t *testing.T, expectError bool, err error) {
	if expectError && err == nil {
		t.Fatalf("expected an error, but got none")
	}
	if !expectError && err != nil {
		t.Fatalf("expected no error, but got one: %+v", err)
	}
}

func TestWriterThenParser(t *testing.T) {
	parser := JSONParser{}
	writer := JSONWriter{}

	tests := map[string]struct {
		filepath             string
		trace                []Step
		expectErrorFromWrite bool
	}{
		"start provider chain": {"parser_testdata/byproducts/start_provider_chain.json", stepStartProviderChain(), false},
	}

	for name, tc := range tests {
		t.Run(name, func(t *testing.T) {
			err := writer.WriteTraceToFile(tc.filepath, tc.trace)

			CheckErrorMatchesExpectation(t, tc.expectErrorFromWrite, err)

			got, err := parser.ReadTraceFromFile(tc.filepath)
			diff := cmp.Diff(tc.trace, got, cmp.AllowUnexported(Step{}))
			if diff != "" {
				t.Fatalf(diff)
			}
		})
	}
}
