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
<<<<<<< HEAD
				t.Fatalf("in testcase %v, got error reading trace from file: %v", name, err)
			}
=======
				t.Fatalf("error reading trace from file: %v", err)
			}

>>>>>>> 24b0ef1b (fix: e2e trace format fails on slashthrottlesteps (#903))
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

func TestMarshalAndUnmarshalChainState(t *testing.T) {
	tests := map[string]struct {
		chainState ChainState
	}{
		"consumer addition proposal": {ChainState{
			ValBalances: &map[ValidatorID]uint{
				ValidatorID("alice"): 9489999999,
				ValidatorID("bob"):   9500000000,
			},
			Proposals: &map[uint]Proposal{
				2: ConsumerAdditionProposal{
					Deposit:       10000001,
					Chain:         ChainID("test"),
					SpawnTime:     0,
					InitialHeight: clienttypes.Height{RevisionNumber: 5, RevisionHeight: 5},
					Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
				},
			},
		}},
		"params-proposal": {ChainState{
			ValBalances: &map[ValidatorID]uint{
				ValidatorID("alice"): 9889999998,
				ValidatorID("bob"):   9960000001,
			},
			Proposals: &map[uint]Proposal{
				1: ParamsProposal{
					Deposit:  10000001,
					Status:   "PROPOSAL_STATUS_VOTING_PERIOD",
					Subspace: "staking",
					Key:      "MaxValidators",
					Value:    "105",
				},
			},
		}},
		"consuemr removal proposal": {ChainState{
			Proposals: &map[uint]Proposal{
				5: ConsumerRemovalProposal{
					Deposit:  10000001,
					Chain:    ChainID("test123"),
					StopTime: 5000000000,
					Status:   "PROPOSAL_STATUS_PASSED",
				},
			},
			ValBalances: &map[ValidatorID]uint{
				ValidatorID("bob"): 9500000000,
			},
			ConsumerChains: &map[ChainID]bool{}, // Consumer chain is now removed
		}},
		"text-proposal": {ChainState{
			ValPowers: &map[ValidatorID]uint{
				ValidatorID("alice"): 509,
				ValidatorID("bob"):   500,
				ValidatorID("carol"): 495,
			},
			ValBalances: &map[ValidatorID]uint{
				ValidatorID("bob"): 9500000000,
			},
			Proposals: &map[uint]Proposal{
				// proposal does not exist
				10: TextProposal{},
			},
		}},
		"equivocation-proposal": {ChainState{
			ValPowers: &map[ValidatorID]uint{
				ValidatorID("alice"): 509,
				ValidatorID("bob"):   500,
				ValidatorID("carol"): 0,
			},
			ValBalances: &map[ValidatorID]uint{
				ValidatorID("bob"): 9489999999,
			},
			Proposals: &map[uint]Proposal{
				5: EquivocationProposal{
					Deposit:          10000001,
					Status:           "PROPOSAL_STATUS_VOTING_PERIOD",
					ConsensusAddress: "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
					Power:            500,
					Height:           10,
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
				log.Print(string(jsonobj))
				t.Fatalf(diff)
			}
		})
	}
}
