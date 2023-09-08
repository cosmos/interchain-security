package main

import (
	"encoding/json"
	"reflect"
	"strings"
	"testing"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/davecgh/go-spew/spew"
)

func TestProposalUnmarshal(t *testing.T) {
	proposalAndTypeString := `{
		"Type": "main.ConsumerAdditionProposal",
		"RawProposal": {
			"Deposit": 10000001,
			"Chain": "consu",
			"SpawnTime": 0,
			"InitialHeight": {
				"revision_height": 1
			},
			"Status": "PROPOSAL_STATUS_PASSED"
		}
	}`

	expectedProposal := ConsumerAdditionProposal{
		Deposit:       10000001,
		Chain:         ChainID("consu"),
		SpawnTime:     0,
		InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
		Status:        "PROPOSAL_STATUS_PASSED",
	}

	propAndType := &ProposalAndType{}
	err := json.Unmarshal([]byte(proposalAndTypeString), propAndType)
	if err != nil {
		t.Errorf("Unexpected error while unmarshalling: %v", err)
	}

	actualProposal, err := UnmarshalProposalWithType(propAndType.RawProposal, propAndType.Type)
	if err != nil {
		t.Errorf("Unexpected error while unmarshalling\n error: %v\n Raw proposal: %v\n Type: %v", err, spew.Sdump(propAndType.RawProposal), propAndType.Type)
	}

	if !reflect.DeepEqual(actualProposal, expectedProposal) {
		t.Errorf("Expected proposal: %v, but got: %v", spew.Sdump(expectedProposal), spew.Sdump(actualProposal))
	}
}

type ChainStateTestCase struct {
	name              string
	jsonBytes         []byte
	chainState        ChainState
	expectedErrorText string
}

var testCases = []ChainStateTestCase{
	{
		name: "valid JSON with proposals",
		jsonBytes: []byte(`{
			"ValBalances": {
				"alice": 9500000000,
				"bob": 9500000000,
				"carol": 9500000000
			},
			"Proposals": {
				"1": {
					"ProposalType": "main.ConsumerAdditionProposal",
					"Proposal": {
						"Deposit": 10000001,
						"Chain": "consu",
						"SpawnTime": 0,
						"InitialHeight": {
							"revision_height": 1
						},
						"Status": "PROPOSAL_STATUS_PASSED"
					}
				}
			}
		}`),
		chainState: ChainState{
			ValBalances: &map[ValidatorID]uint{
				ValidatorID("alice"): 9500000000,
				ValidatorID("bob"):   9500000000,
				ValidatorID("carol"): 9500000000,
			},
			Proposals: &map[uint]Proposal{
				1: ConsumerAdditionProposal{
					Deposit:       10000001,
					Chain:         ChainID("consu"),
					SpawnTime:     0,
					InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
					Status:        "PROPOSAL_STATUS_PASSED",
				},
			},
		},
		expectedErrorText: "",
	},
	{
		name:              "invalid JSON",
		jsonBytes:         []byte(`thisisnotagoodjsonstring`),
		expectedErrorText: "invalid json",
	},
	{
		name: "unknown proposal type",
		jsonBytes: []byte(`{
			"ValBalances": {
				"alice": 9500000000,
				"bob": 9500000000,
				"carol": 9500000000
			},
			"Proposals": {
				"1": {
					"ProposalType": "main.NotAProposalTypeProposal",
					"Proposal": {
						"Deposit": 10000001,
						"Chain": "consu",
						"SpawnTime": 0,
						"InitialHeight": {
							"revision_height": 1
						},
						"Status": "PROPOSAL_STATUS_PASSED"
					}
				}
			},
		}`),
		expectedErrorText: "not a known proposal type",
	},
}

func TestUnmarshalJSON(t *testing.T) {
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			var result ChainState
			err := result.UnmarshalJSON(tc.jsonBytes)
			if err != nil && tc.expectedErrorText == "" {
				t.Errorf("Unexpected error: %v", err)
			}

			if err == nil && tc.expectedErrorText != "" {
				t.Errorf("Expected error to contain: %v, but got no error", tc.expectedErrorText)
			}

			if err != nil && tc.expectedErrorText != "" && strings.Contains(err.Error(), tc.expectedErrorText) {
				t.Errorf("Expected error to contain: %v, but got: %v", tc.expectedErrorText, err)
			}

			if !reflect.DeepEqual(result, tc.chainState) {
				t.Errorf("Expected ChainState: %v, but got: %v", tc.chainState, result)
			}
		})
	}
}

func TestMarshalJSON(t *testing.T) {
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result, err := tc.chainState.MarshalJSON()
			if err != nil && tc.expectedErrorText == "" {
				t.Errorf("Unexpected error: %v", err)
			}

			if err == nil && tc.expectedErrorText != "" {
				t.Errorf("Expected error to contain: %v, but got no error", tc.expectedErrorText)
			}

			if err != nil && tc.expectedErrorText != "" && strings.Contains(err.Error(), tc.expectedErrorText) {
				t.Errorf("Expected error to contain: %v, but got: %v", tc.expectedErrorText, err)
			}

			if !reflect.DeepEqual(result, tc.jsonBytes) {
				t.Errorf("Expected JSON: %v, but got: %v", string(tc.jsonBytes), string(result))
			}
		})
	}
}
