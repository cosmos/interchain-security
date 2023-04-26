package main

import (
	"encoding/json"
	"log"
	"os"
	"path/filepath"
	"testing"

	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	"github.com/google/go-cmp/cmp"
)

// Checks that writing, then parsing a trace results in the same trace.
func TestWriterThenParser(t *testing.T) {
	parser := JSONParser{}
	writer := JSONWriter{}

	tests := map[string]struct {
		trace []Step
	}{
		"start_provider_chain": {stepStartProviderChain()},
		"happyPath":            {happyPathSteps},
		"democracy":            {democracySteps},
		"slashThrottleSteps":   {slashThrottleSteps},
		"multipleConsumers":    {multipleConsumers},
	}

	dir, err := os.MkdirTemp("", "example")
	if err != nil {
		log.Fatal(err)
	}
	defer os.RemoveAll(dir) // clean up

	for name, tc := range tests {
		t.Run(name, func(t *testing.T) {
			filename := filepath.Join(dir, name)
			err := writer.WriteTraceToFile(filename, tc.trace)
			if err != nil {
				t.Fatalf("error writing trace to file: %v", err)
			}

			got, err := parser.ReadTraceFromFile(filename)
			if err != nil {
				t.Fatalf("error reading trace from file: %v", err)
			}

			diff := cmp.Diff(tc.trace, got, cmp.AllowUnexported(Step{}))
			if diff != "" {
				t.Fatalf(diff)
			}
		})
	}
}

// Checks that writing a trace does not result in an error.
func TestWriteExamples(t *testing.T) {
	writer := JSONWriter{}

	tests := map[string]struct {
		trace []Step
	}{
		"start_provider_chain": {stepStartProviderChain()},
		"happyPath":            {happyPathSteps},
		"democracy":            {democracySteps},
		"slashThrottleSteps":   {slashThrottleSteps},
		"multipleConsumers":    {multipleConsumers},
	}

	dir := "tracehandler_testdata"

	for name, tc := range tests {
		t.Run(name, func(t *testing.T) {
			filename := filepath.Join(dir, name+".json")
			err := writer.WriteTraceToFile(filename, tc.trace)
			if err != nil {
				t.Fatalf("error writing trace to file: %v", err)
			}
		})
	}
}

func TestMarshalAndUnmarshalChainState(t *testing.T) {
	tests := map[string]struct {
		chainState ChainState
	}{
		"start_provider_chain": {ChainState{
			ValBalances: &map[ValidatorID]uint{
				ValidatorID("alice"): 9489999999,
				ValidatorID("bob"):   9500000000,
			},
			Proposals: &map[uint]Proposal{
				2: ConsumerAdditionProposal{
					Deposit:       10000001,
					Chain:         ChainID("test"),
					SpawnTime:     0,
					InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
					Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
				},
			},
		}},
	}

	for name, tc := range tests {
		t.Run(name, func(t *testing.T) {
			jsonobj, err := json.Marshal(tc.chainState)
			if err != nil {
				t.Fatalf("error marshalling chain state: %v", err)
			}

			var got *ChainState
			err = json.Unmarshal(jsonobj, &got)
			if err != nil {
				t.Fatalf("error unmarshalling chain state: %v", err)
			}

			diff := cmp.Diff(tc.chainState, *got)
			if diff != "" {
				t.Fatalf(diff)
			}
		})
	}
}
