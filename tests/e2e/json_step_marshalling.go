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
		Action     map[string]any
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

// UnmarshalMapToActionType takes a JSON object and an action type and marshals into an object of the corresponding action.
func UnmarshalMapToActionType(inputMap map[string]any, actionType string) (interface{}, error) {
	switch actionType {
	case "main.StartChainAction":
		var action StartChainAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.SendTokensAction":
		var action SendTokensAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.submitTextProposalAction":
		var action submitTextProposalAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.submitConsumerAdditionProposalAction":
		var action submitConsumerAdditionProposalAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.submitConsumerRemovalProposalAction":
		var action submitConsumerRemovalProposalAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.submitEquivocationProposalAction":
		var action submitEquivocationProposalAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.submitParamChangeProposalAction":
		var action submitParamChangeProposalAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.voteGovProposalAction":
		var action voteGovProposalAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.startConsumerChainAction":
		var action startConsumerChainAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.addChainToRelayerAction":
		var action addChainToRelayerAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.addIbcConnectionAction":
		var action addIbcConnectionAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil

	case "main.addIbcChannelAction":
		var action addIbcChannelAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil

	case "main.transferChannelCompleteAction":
		var action transferChannelCompleteAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil

	case "main.relayPacketsAction":
		var action relayPacketsAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil

	case "main.relayRewardPacketsToProviderAction":
		var action relayRewardPacketsToProviderAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil

	case "main.delegateTokensAction":
		var action delegateTokensAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil

	case "main.unbondTokensAction":
		var action unbondTokensAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil

	case "main.redelegateTokensAction":
		var action redelegateTokensAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.downtimeSlashAction":
		var action downtimeSlashAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.unjailValidatorAction":
		var action unjailValidatorAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.doublesignSlashAction":
		var action doublesignSlashAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.registerRepresentativeAction":
		var action registerRepresentativeAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.assignConsumerPubKeyAction":
		var action assignConsumerPubKeyAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.slashThrottleDequeue":
		var action slashThrottleDequeue
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	case "main.startHermesAction":
		var action startHermesAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	default:
		return nil, fmt.Errorf("%s is not a known action type", actionType)
	}
}
