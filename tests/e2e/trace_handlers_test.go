package main

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"testing"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/google/go-cmp/cmp"
)

// an isolated test case for a proposal submission
var proposalSubmissionSteps = []Step{
	{submitTextProposalAction{Title: "Proposal 1", Description: "Description 1"}, State{}},
}

// an isolated test case for a state check involving a proposal
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
	tests := map[string]struct {
		trace []Step
	}{
		"proposalSubmission":    {proposalSubmissionSteps},
		"proposalInState":       {proposalInStateSteps},
		"start_provider_chain":  {stepStartProviderChain()},
		"happyPath":             {happyPathSteps},
		"democracy":             {democracySteps},
		"slashThrottle":         {slashThrottleSteps},
		"multipleConsumers":     {multipleConsumers},
		"shorthappy":            {shortHappyPathSteps},
		"democracyRewardsSteps": {democracyRewardsSteps},
		"changeover":            {changeoverSteps},
	}

	dir, err := os.MkdirTemp("", "example")
	if err != nil {
		log.Fatal(err)
	}
	defer os.RemoveAll(dir) // clean up

	for name, tc := range tests {
		t.Run(name, func(t *testing.T) {
			filename := filepath.Join(dir, "trace.json")
			err := WriteReadCompareTrace(tc.trace, filename, name)
			if err != nil {
				log.Fatal(err)
			}
		})
	}
}

// Write a trace to a file, then reads it back and compares to the original.
func WriteReadCompareTrace(trace []Step, filename, name string) error {
	err := WriteAndReadTrace(GlobalJSONParser, GlobalJSONWriter, trace, filename)
	if err != nil {
		return fmt.Errorf("in testcase %v, got error writing trace to file: %v", name, err)
	}

	got, err := GlobalJSONParser.ReadTraceFromFile(filename)
	if err != nil {
		return fmt.Errorf("in testcase %v, got error reading trace from file: %v", name, err)
	}
	diff := cmp.Diff(trace, got, cmp.AllowUnexported(Step{}))
	if diff != "" {
		return fmt.Errorf("Got a difference for testcase %s (-want +got):\n%s", name, diff)
	}

	return nil
}

// Checks that writing a trace does not result in an error.
func TestWriteExamples(t *testing.T) {
	tests := map[string]struct {
		trace []Step
	}{
		"start_provider_chain":  {stepStartProviderChain()},
		"happyPath":             {happyPathSteps},
		"democracy":             {democracySteps},
		"slashThrottle":         {slashThrottleSteps},
		"multipleConsumers":     {multipleConsumers},
		"shorthappy":            {shortHappyPathSteps},
		"democracyRewardsSteps": {democracyRewardsSteps},
		"changeover":            {changeoverSteps},
	}

	dir := "tracehandler_testdata"

	for name, tc := range tests {
		t.Run(name, func(t *testing.T) {
			filename := filepath.Join(dir, name+".json")
			err := GlobalJSONWriter.WriteTraceToFile(filename, tc.trace)
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
			err := MarshalAndUnmarshalChainState(tc.chainState)
			if err != nil {
				t.Fatalf(err.Error())
			}
		})
	}
}

func MarshalAndUnmarshalChainState(chainState ChainState) error {
	jsonobj, err := json.Marshal(chainState)
	if err != nil {
		return fmt.Errorf("error marshalling chain state: %v", err)
	}

	var got *ChainState
	err = json.Unmarshal(jsonobj, &got)
	if err != nil {
		return fmt.Errorf("error unmarshalling chain state: %v", err)
	}

	diff := cmp.Diff(chainState, *got)
	if diff != "" {
		log.Print(string(jsonobj))
		return fmt.Errorf(diff)
	}

	return nil
}

func WriteAndReadTrace(parser TraceParser, writer TraceWriter, trace []Step, tmp_filepath string) error {
	err := writer.WriteTraceToFile(tmp_filepath, trace)
	if err != nil {
		return fmt.Errorf("error writing trace to file: %v", err)
	}

	got, err := parser.ReadTraceFromFile(tmp_filepath)
	if err != nil {
		return fmt.Errorf("error reading trace from file: %v", err)
	}

	diff := cmp.Diff(trace, got, cmp.AllowUnexported(Step{}))
	if diff != "" {
		return fmt.Errorf(diff)
	}

	return nil
}
