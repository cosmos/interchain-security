package main

import (
	"fmt"

	"github.com/mitchellh/mapstructure"
)

// StepWithActionType is a utility class that wraps a Step together with its action type. Used to marshal/unmarshal
type StepWithActionType struct {
	Step
	ActionType string `json:"ActionType"`
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
	case "main.submitParamChangeLegacyProposalAction":
		var action submitParamChangeLegacyProposalAction
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
	case "main.AddChainToRelayerAction":
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
	case "main.startRelayerAction":
		var action startRelayerAction
		err := mapstructure.Decode(inputMap, &action)
		if err != nil {
			return nil, err
		}
		return action, nil
	default:
		return nil, fmt.Errorf("%s is not a known action type", actionType)
	}
}
