package main

import (
	"fmt"
	"reflect"

	"github.com/mitchellh/mapstructure"
)

// StepWithActionType is a utility class that wraps a Step together with its action type. Used to marshal/unmarshal
type StepWithActionType struct {
	Step
	ActionType string `json:"ActionType"`
}

// has to be manually kept in sync with the available action types.
var actionRegistry = map[string]reflect.Type{
	"main.submitConsumerAdditionProposalAction":  reflect.TypeOf(submitConsumerAdditionProposalAction{}),
	"main.StartChainAction":                      reflect.TypeOf(StartChainAction{}),
	"main.SendTokensAction":                      reflect.TypeOf(SendTokensAction{}),
	"main.submitTextProposalAction":              reflect.TypeOf(submitTextProposalAction{}),
	"main.submitConsumerRemovalProposalAction":   reflect.TypeOf(submitConsumerRemovalProposalAction{}),
	"main.submitEquivocationProposalAction":      reflect.TypeOf(submitEquivocationProposalAction{}),
	"main.submitParamChangeLegacyProposalAction": reflect.TypeOf(submitParamChangeLegacyProposalAction{}),
	"main.voteGovProposalAction":                 reflect.TypeOf(voteGovProposalAction{}),
	"main.startConsumerChainAction":              reflect.TypeOf(startConsumerChainAction{}),
	"main.AddChainToRelayerAction":               reflect.TypeOf(addChainToRelayerAction{}),
	"main.addIbcConnectionAction":                reflect.TypeOf(addIbcConnectionAction{}),
	"main.addIbcChannelAction":                   reflect.TypeOf(addIbcChannelAction{}),
	"main.transferChannelCompleteAction":         reflect.TypeOf(transferChannelCompleteAction{}),
	"main.unjailValidatorAction":                 reflect.TypeOf(unjailValidatorAction{}),
	"main.assignConsumerPubKeyAction":            reflect.TypeOf(assignConsumerPubKeyAction{}),
	"main.delegateTokensAction":                  reflect.TypeOf(delegateTokensAction{}),
	"main.relayPacketsAction":                    reflect.TypeOf(relayPacketsAction{}),
	"main.registerRepresentativeAction":          reflect.TypeOf(registerRepresentativeAction{}),
	"main.relayRewardPacketsToProviderAction":    reflect.TypeOf(relayRewardPacketsToProviderAction{}),
	"main.registerConsumerRewardDenomAction":     reflect.TypeOf(registerConsumerRewardDenomAction{}),
	"main.downtimeSlashAction":                   reflect.TypeOf(downtimeSlashAction{}),
	"main.unbondTokensAction":                    reflect.TypeOf(unbondTokensAction{}),
	"main.cancelUnbondTokensAction":              reflect.TypeOf(cancelUnbondTokensAction{}),
	"main.redelegateTokensAction":                reflect.TypeOf(redelegateTokensAction{}),
	"main.doublesignSlashAction":                 reflect.TypeOf(doublesignSlashAction{}),
	"main.startRelayerAction":                    reflect.TypeOf(startRelayerAction{}),
	"main.slashThrottleDequeue":                  reflect.TypeOf(slashThrottleDequeue{}),
	"main.createIbcClientsAction":                reflect.TypeOf(createIbcClientsAction{}),
	"main.LegacyUpgradeProposalAction":           reflect.TypeOf(LegacyUpgradeProposalAction{}),
	"main.waitUntilBlockAction":                  reflect.TypeOf(waitUntilBlockAction{}),
	"main.ChangeoverChainAction":                 reflect.TypeOf(ChangeoverChainAction{}),
	"main.StartSovereignChainAction":             reflect.TypeOf(StartSovereignChainAction{}),
}

// UnmarshalMapToActionType takes a JSON object and an action type and marshals into an object of the corresponding action.
func UnmarshalMapToActionType(inputMap map[string]any, actionType string) (interface{}, error) {
	reflectType, ok := actionRegistry[actionType]
	if !ok {
		return nil, fmt.Errorf("%s is not a known action type", actionType)
	}
	action := reflect.New(reflectType).Interface()
	err := mapstructure.Decode(inputMap, &action)
	if err != nil {
		return nil, err
	}
	return action, nil
}
