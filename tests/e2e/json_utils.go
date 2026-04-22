package main

import (
	"encoding/json"
	"fmt"
	"reflect"
	"strings"
)

// normalizeActionReflectType maps reflect.TypeOf(action).String() to a stable key.
// Type aliases in package main for structs defined in testlib resolve as "e2e.*",
// while unmarshalling historically used the "main.*" prefix.
func normalizeActionReflectType(actionTypeString string) string {
	switch {
	case strings.HasPrefix(actionTypeString, "main."):
		return strings.TrimPrefix(actionTypeString, "main.")
	case strings.HasPrefix(actionTypeString, "e2e."):
		return strings.TrimPrefix(actionTypeString, "e2e.")
	default:
		return actionTypeString
	}
}

// MarshalJSON marshals a step into JSON while including the type of the action.
func (step Step) MarshalJSON() ([]byte, error) {
	actionType := reflect.TypeOf(step.Action)

	result := struct {
		ActionType string
		Action     interface{}
		State      State
	}{
		ActionType: actionType.String(),
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

// UnmarshalMapToActionType takes a JSON object and an action type and marshals into an object of the corresponding action.
func UnmarshalMapToActionType(rawAction json.RawMessage, actionTypeString string) (interface{}, error) {
	actionTypeString = normalizeActionReflectType(actionTypeString)
	var err error
	switch actionTypeString {
	case "SubmitConsumerAdditionProposalAction":
		var a SubmitConsumerAdditionProposalAction
		err = json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "SubmitConsumerModificationProposalAction":
		var a SubmitConsumerModificationProposalAction
		err = json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "CreateConsumerChainAction":
		var a CreateConsumerChainAction
		err = json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "UpdateConsumerChainAction":
		var a UpdateConsumerChainAction
		err = json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "RemoveConsumerChainAction":
		var a RemoveConsumerChainAction
		err = json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "OptInAction":
		var a OptInAction
		err = json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "OptOutAction":
		var a OptOutAction
		err = json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "SetConsumerCommissionRateAction":
		var a SetConsumerCommissionRateAction
		err = json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "SendTokensAction":
		var a SendTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "StartChainAction":
		var a StartChainAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "SubmitTextProposalAction":
		var a SubmitTextProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "SubmitConsumerRemovalProposalAction":
		var a SubmitConsumerRemovalProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "SubmitEnableTransfersProposalAction":
		var a SubmitEnableTransfersProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "VoteGovProposalAction":
		var a VoteGovProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "StartConsumerChainAction":
		var a StartConsumerChainAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "AddChainToRelayerAction":
		var a AddChainToRelayerAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "AddIbcConnectionAction":
		var a AddIbcConnectionAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "AddIbcChannelAction":
		var a AddIbcChannelAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "TransferChannelCompleteAction":
		var a TransferChannelCompleteAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "UnjailValidatorAction":
		var a UnjailValidatorAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "AssignConsumerPubKeyAction":
		var a AssignConsumerPubKeyAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "DelegateTokensAction":
		var a DelegateTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "RelayPacketsAction":
		var a RelayPacketsAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "RegisterRepresentativeAction":
		var a RegisterRepresentativeAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "RelayRewardPacketsToProviderAction":
		var a RelayRewardPacketsToProviderAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "SubmitChangeRewardDenomsProposalAction":
		var a SubmitChangeRewardDenomsProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "DowntimeSlashAction":
		var a DowntimeSlashAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "UnbondTokensAction":
		var a UnbondTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "CancelUnbondTokensAction":
		var a CancelUnbondTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "RedelegateTokensAction":
		var a RedelegateTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "DoublesignSlashAction":
		var a DoublesignSlashAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "StartRelayerAction":
		var a StartRelayerAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "SlashMeterReplenishmentAction":
		var a SlashMeterReplenishmentAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "WaitTimeAction":
		var a WaitTimeAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "CreateIbcClientsAction":
		var a CreateIbcClientsAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "CreateIbcClientAction":
		var a CreateIbcClientAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "TransferIbcTokenAction":
		var a TransferIbcTokenAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "LightClientEquivocationAttackAction":
		var a LightClientEquivocationAttackAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "LightClientAmnesiaAttackAction":
		var a LightClientAmnesiaAttackAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "LightClientLunaticAttackAction":
		var a LightClientLunaticAttackAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "ForkConsumerChainAction":
		var a ForkConsumerChainAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "DetectConsumerEvidenceAction":
		var a DetectConsumerEvidenceAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "SubmitConsumerMisbehaviourAction":
		var a SubmitConsumerMisbehaviourAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "UpdateLightClientAction":
		var a UpdateLightClientAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	default:
		return nil, fmt.Errorf("unknown action type: %s", actionTypeString)
	}
	return nil, err
}
