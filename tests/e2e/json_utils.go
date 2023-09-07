package main

import (
	"encoding/json"
	"fmt"
	"reflect"

	"github.com/mitchellh/mapstructure"
)

// MarshalJSON marshals a step into JSON while including the type of the action.
func (step Step) MarshalJSON() ([]byte, error) {
	actionType := reflect.TypeOf(step.Action).String()

	result := struct {
		ActionType string
		Action     interface{}
		State      State
	}{
		ActionType: actionType,
		Action:     step.Action,
		State:      step.State,
	}

	return json.Marshal(result)
}

// UnmarshalJSON unmarshals a step from JSON while including the type of the action.
func (step *Step) UnmarshalJSON(data []byte) error {
	var tmp struct {
		ActionType string
		Action     json.RawMessage
		State      State
	}
	if err := json.Unmarshal(data, &tmp); err != nil {
		return err
	}

	action, err := UnmarshalMapToActionType(tmp.Action, tmp.ActionType)
	if err != nil {
		return err
	}

	step.Action = action
	step.State = tmp.State
	return nil
}

// has to be manually kept in sync with the available action types.
var actionRegistry = map[string]interface{}{
	"main.submitConsumerAdditionProposalAction":  submitConsumerAdditionProposalAction{},
	"main.StartChainAction":                      StartChainAction{},
	"main.SendTokensAction":                      SendTokensAction{},
	"main.submitTextProposalAction":              submitTextProposalAction{},
	"main.submitConsumerRemovalProposalAction":   submitConsumerRemovalProposalAction{},
	"main.submitEquivocationProposalAction":      submitEquivocationProposalAction{},
	"main.submitParamChangeLegacyProposalAction": submitParamChangeLegacyProposalAction{},
	"main.voteGovProposalAction":                 voteGovProposalAction{},
	"main.startConsumerChainAction":              startConsumerChainAction{},
	"main.AddChainToRelayerAction":               addChainToRelayerAction{},
	"main.addIbcConnectionAction":                addIbcConnectionAction{},
	"main.addIbcChannelAction":                   addIbcChannelAction{},
	"main.transferChannelCompleteAction":         transferChannelCompleteAction{},
	"main.unjailValidatorAction":                 unjailValidatorAction{},
	"main.assignConsumerPubKeyAction":            assignConsumerPubKeyAction{},
	"main.delegateTokensAction":                  delegateTokensAction{},
	"main.relayPacketsAction":                    relayPacketsAction{},
	"main.registerRepresentativeAction":          registerRepresentativeAction{},
	"main.relayRewardPacketsToProviderAction":    relayRewardPacketsToProviderAction{},
	"main.registerConsumerRewardDenomAction":     registerConsumerRewardDenomAction{},
	"main.downtimeSlashAction":                   downtimeSlashAction{},
	"main.unbondTokensAction":                    unbondTokensAction{},
	"main.cancelUnbondTokensAction":              cancelUnbondTokensAction{},
	"main.redelegateTokensAction":                redelegateTokensAction{},
	"main.doublesignSlashAction":                 doublesignSlashAction{},
	"main.startRelayerAction":                    startRelayerAction{},
	"main.slashThrottleDequeue":                  slashThrottleDequeue{},
	"main.createIbcClientsAction":                createIbcClientsAction{},
	"main.LegacyUpgradeProposalAction":           LegacyUpgradeProposalAction{},
	"main.waitUntilBlockAction":                  waitUntilBlockAction{},
	"main.ChangeoverChainAction":                 ChangeoverChainAction{},
	"main.StartSovereignChainAction":             StartSovereignChainAction{},
}

// UnmarshalMapToActionType takes a JSON object and an action type and marshals into an object of the corresponding action.
func UnmarshalMapToActionType(inputMap json.RawMessage, actionType string) (interface{}, error) {
	actionStruct, ok := actionRegistry[actionType]
	if !ok {
		return nil, fmt.Errorf("%s is not a known action type", actionType)
	}
	err := mapstructure.Decode(inputMap, &actionStruct)
	if err != nil {
		return nil, err
	}
	return actionStruct, nil
}

// for marshalling/unmarshalling proposals
type ProposalAndType struct {
	RawProposal map[string]any
	Type        string `json:"Type"`
}

type ChainStateWithProposalTypes struct {
	ChainState
	Proposals *map[uint]ProposalAndType `json:"Proposals"`
}

// custom marshal and unmarshal functions for the chainstate that convert proposals to/from the auxiliary type with type info

// transform the ChainState into a ChainStateWithProposalTypes by adding type info to the proposals
func (c *ChainState) MarshalJson() ([]byte, error) {
	fmt.Println("Custom marshal is called")
	chainStateWithProposalTypes := ChainStateWithProposalTypes{
		ChainState: *c,
	}
	if c.Proposals != nil {
		proposalsWithTypes := make(map[uint]ProposalAndType)
		for k, v := range *c.Proposals {
			rawProposal := make(map[string]any)
			err := mapstructure.Decode(v, &rawProposal)
			if err != nil {
				return nil, err
			}
			proposalsWithTypes[k] = ProposalAndType{rawProposal, reflect.TypeOf(v).String()}
		}
		chainStateWithProposalTypes.Proposals = &proposalsWithTypes
	}
	return json.Marshal(chainStateWithProposalTypes)
}

// unmarshal the ChainStateWithProposalTypes into a ChainState by removing the type info from the proposals and getting back standard proposals
func (c *ChainState) UnmarshalJson(data []byte) error {
	fmt.Println("Custom unmarshal is called")

	chainStateWithProposalTypes := ChainStateWithProposalTypes{}
	err := json.Unmarshal(data, &chainStateWithProposalTypes)
	if err != nil {
		return err
	}
	*c = chainStateWithProposalTypes.ChainState
	if chainStateWithProposalTypes.Proposals != nil {
		proposals := make(map[uint]Proposal)
		for k, v := range *chainStateWithProposalTypes.Proposals {
			proposal, err := UnmarshalProposalWithType(v.RawProposal, v.Type)
			if err != nil {
				return err
			}
			proposals[k] = proposal
		}
		c.Proposals = &proposals
	}
	return nil
}

// has to be manually kept in sync with the available proposal types.
var proposalRegistry = map[string]Proposal{
	"main.TextProposal":             TextProposal{},
	"main.ConsumerAdditionProposal": ConsumerAdditionProposal{},
	"main.UpgradeProposal":          UpgradeProposal{},
	"main.ConsumerRemovalProposal":  ConsumerRemovalProposal{},
	"main.EquivocationProposal":     EquivocationProposal{},
	"main.ParamsProposal":           ParamsProposal{},
}

// UnmarshalProposalWithType takes a JSON object and a proposal type and marshals into an object of the corresponding proposal.
func UnmarshalProposalWithType(inputMap map[string]any, proposalType string) (Proposal, error) {
	propStruct, ok := proposalRegistry[proposalType]
	if !ok {
		return nil, fmt.Errorf("%s is not a known proposal type", proposalType)
	}
	err := mapstructure.Decode(inputMap, &propStruct)
	if err != nil {
		return nil, err
	}
	return propStruct, nil
}
