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

	type ProposalAndType struct {
		RawProposal json.RawMessage
		Type        string
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
	name                       string
	jsonBytes                  []byte
	chainState                 ChainState
	expectedUnmarshalErrorText string
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
		expectedUnmarshalErrorText: "",
	},
	{
		name:                       "invalid JSON",
		jsonBytes:                  []byte(`thisisnotagoodjsonstring`),
		expectedUnmarshalErrorText: "invalid json",
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
					"Type": "main.NotAProposalTypeProposal",
					"RawProposal": {
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
		expectedUnmarshalErrorText: "not a known proposal type",
	},
}

func TestUnmarshalJSON(t *testing.T) {
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			var result ChainState
			err := result.UnmarshalJSON(tc.jsonBytes)
			if err != nil && tc.expectedUnmarshalErrorText == "" {
				t.Errorf("Test case %v: Unexpected error: %v", tc.name, err)
			}

			if err == nil && tc.expectedUnmarshalErrorText != "" {
				t.Errorf("Test case %v: Expected error to contain: %v, but got no error", tc.name, tc.expectedUnmarshalErrorText)
			}

			if err != nil && tc.expectedUnmarshalErrorText != "" && strings.Contains(err.Error(), tc.expectedUnmarshalErrorText) {
				t.Errorf("Test case %v: Expected error to contain: %v, but got: %v", tc.name, tc.expectedUnmarshalErrorText, err)
			}

			if !reflect.DeepEqual(result, tc.chainState) {
				t.Errorf("Test case %v: Expected ChainState: %v, but got: %v", tc.name, tc.chainState, result)
			}
		})
	}
}

func TestMarshalJSON(t *testing.T) {
	// checks that marshalling and unmarshalling is the identity
	// would optimally check that the marshalled JSON is the same as the expected JSON,
	// but the marshalled JSON will specifically list null fields
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result, err := tc.chainState.MarshalJSON()
			if err != nil {
				t.Errorf("Test case %v: Unexpected error while marshalling: %v", tc.name, err)
			}

			if tc.expectedUnmarshalErrorText != "" {
				// unmarshalling to compare does not make sense, since we expect it to
				// fail, so just test that marshalling works and continue
				return
			}

			unmarshalledResult := ChainState{}
			err = unmarshalledResult.UnmarshalJSON(result)
			if err != nil {
				t.Errorf("Test case %v: Unexpected error while unmarshalling: %v", tc.name, err)
			}

			if !reflect.DeepEqual(unmarshalledResult, tc.chainState) {
				t.Errorf("Test case %v: Expected: %v, but got: %v", tc.name, string(tc.jsonBytes), string(result))
			}
		})
	}
}
