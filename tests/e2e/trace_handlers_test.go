package main

import (
	"log"
	"os"
	"path/filepath"
	"testing"

	"github.com/google/go-cmp/cmp"
)

// tests unmarshalling and marshalling a ChainState object
func TestMarshal(t *testing.T) {
}

// define some sets of steps to test with
var proposalSubmissionSteps = []Step{
	{submitTextProposalAction{Title: "Proposal 1", Description: "Description 1"}, State{}},
}

var proposalInStateSteps = []Step{
	{
		Action: submitConsumerRemovalProposalAction{},
		State: State{
			ChainID("provi"): ChainState{
				Proposals: &map[uint]Proposal{
					1: ConsumerRemovalProposal{
						Deposit:  10000001,
						Chain:    ChainID("foo"),
						StopTime: 0,
						Status:   "PROPOSAL_STATUS_VOTING_PERIOD",
					},
				},
			},
		},
	},
}

// Checks that writing, then parsing a trace results in the same trace.
func TestWriterThenParser(t *testing.T) {
	parser := JSONParser{}
	writer := JSONWriter{}

	tests := map[string]struct {
		trace []Step
	}{
		"proposalSubmission":   {proposalSubmissionSteps},
		"proposalInState":      {proposalInStateSteps},
		"start_provider_chain": {stepStartProviderChain()},
		// "happyPath":            {happyPathSteps},
		// "democracy":            {democracySteps},
		// "slashThrottle":        {slashThrottleSteps},
		// "multipleConsumers":    {multipleConsumers},
		// "shorthappy":           {shortHappyPathSteps},
		// "rewardDenomConsumer":  {rewardDenomConsumerSteps},
		// "changeover":           {changeoverSteps},
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
				t.Fatalf("in testcase %v, got error writing trace to file: %v", name, err)
			}

			got, err := parser.ReadTraceFromFile(filename)
			if err != nil {
				t.Fatalf("in testcase %v, got error reading trace from file: %v", name, err)
			}
			diff := cmp.Diff(tc.trace, got, cmp.AllowUnexported(Step{}))
			if diff != "" {
				t.Log("Got a difference for testcase " + name)
				t.Errorf("(-want +got):\n%s", diff)
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
		"slashThrottle":        {slashThrottleSteps},
		"multipleConsumers":    {multipleConsumers},
		"shorthappy":           {shortHappyPathSteps},
		"rewardDenomConsumer":  {rewardDenomConsumerSteps},
		"changeover":           {changeoverSteps},
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
