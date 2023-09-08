package main

import (
	"encoding/json"
	"fmt"
	"reflect"
)

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

// has to be manually kept in sync with the available action types.
var actionRegistry = map[string]reflect.Type{
	"main.submitConsumerAdditionProposalAction":  reflect.TypeOf(submitConsumerAdditionProposalAction{}),
	"main.SendTokensAction":                      reflect.TypeOf(SendTokensAction{}),
	"main.StartChainAction":                      reflect.TypeOf(StartChainAction{}),
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
func UnmarshalMapToActionType(rawAction json.RawMessage, actionTypeString string) (interface{}, error) {
	actionType, ok := actionRegistry[actionTypeString]
	if !ok {
		return nil, fmt.Errorf("%s is not a known action type", actionTypeString)
	}

	actionStruct := reflect.Zero(actionType).Interface()
	err := json.Unmarshal(rawAction, &actionStruct)
	if err != nil {
		return nil, err
	}
	return actionStruct, nil
}

// custom marshal and unmarshal functions for the chainstate that convert proposals to/from the auxiliary type with type info

// transform the ChainState into a ChainStateWithProposalTypes by adding type info to the proposals
func (c ChainState) MarshalJSON() ([]byte, error) {
	type ProposalAndType struct {
		RawProposal interface{}
		Type        string
	}

	type ChainStateWithProposalTypes struct {
		ValBalances                    *map[ValidatorID]uint
		ValPowers                      *map[ValidatorID]uint
		RepresentativePowers           *map[ValidatorID]uint
		Params                         *[]Param
		Rewards                        *Rewards
		ConsumerChains                 *map[ChainID]bool
		AssignedKeys                   *map[ValidatorID]string
		ProviderKeys                   *map[ValidatorID]string
		ConsumerChainQueueSizes        *map[ChainID]uint
		GlobalSlashQueueSize           *uint
		RegisteredConsumerRewardDenoms *[]string
		Proposals                      *map[uint]ProposalAndType // the only thing changed from the real ChainState
	}

	chainStateWithProposalTypes := ChainStateWithProposalTypes{
		ValBalances:                    c.ValBalances,
		ValPowers:                      c.ValPowers,
		RepresentativePowers:           c.RepresentativePowers,
		Params:                         c.Params,
		Rewards:                        c.Rewards,
		ConsumerChains:                 c.ConsumerChains,
		AssignedKeys:                   c.AssignedKeys,
		ProviderKeys:                   c.ProviderKeys,
		ConsumerChainQueueSizes:        c.ConsumerChainQueueSizes,
		GlobalSlashQueueSize:           c.GlobalSlashQueueSize,
		RegisteredConsumerRewardDenoms: c.RegisteredConsumerRewardDenoms,
	}
	if c.Proposals != nil {
		proposalsWithTypes := make(map[uint]ProposalAndType)
		for k, v := range *c.Proposals {
			proposalsWithTypes[k] = ProposalAndType{v, reflect.TypeOf(v).String()}
		}
		chainStateWithProposalTypes.Proposals = &proposalsWithTypes
	}
	return json.Marshal(chainStateWithProposalTypes)
}

// unmarshal the ChainStateWithProposalTypes into a ChainState by removing the type info from the proposals and getting back standard proposals
func (c *ChainState) UnmarshalJSON(data []byte) error {
	type ProposalAndType struct {
		RawProposal json.RawMessage
		Type        string
	}

	type ChainStateWithProposalTypes struct {
		ValBalances                    *map[ValidatorID]uint
		ValPowers                      *map[ValidatorID]uint
		RepresentativePowers           *map[ValidatorID]uint
		Params                         *[]Param
		Rewards                        *Rewards
		ConsumerChains                 *map[ChainID]bool
		AssignedKeys                   *map[ValidatorID]string
		ProviderKeys                   *map[ValidatorID]string
		ConsumerChainQueueSizes        *map[ChainID]uint
		GlobalSlashQueueSize           *uint
		RegisteredConsumerRewardDenoms *[]string
		Proposals                      *map[uint]ProposalAndType // the only thing changed from the real ChainState
	}

	chainStateWithProposalTypes := ChainStateWithProposalTypes{}
	err := json.Unmarshal(data, &chainStateWithProposalTypes)
	if err != nil {
		return err
	}
	c.ValBalances = chainStateWithProposalTypes.ValBalances
	c.ValPowers = chainStateWithProposalTypes.ValPowers
	c.RepresentativePowers = chainStateWithProposalTypes.RepresentativePowers
	c.Params = chainStateWithProposalTypes.Params
	c.Rewards = chainStateWithProposalTypes.Rewards
	c.ConsumerChains = chainStateWithProposalTypes.ConsumerChains
	c.AssignedKeys = chainStateWithProposalTypes.AssignedKeys
	c.ProviderKeys = chainStateWithProposalTypes.ProviderKeys
	c.ConsumerChainQueueSizes = chainStateWithProposalTypes.ConsumerChainQueueSizes
	c.GlobalSlashQueueSize = chainStateWithProposalTypes.GlobalSlashQueueSize
	c.RegisteredConsumerRewardDenoms = chainStateWithProposalTypes.RegisteredConsumerRewardDenoms

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
func UnmarshalProposalWithType(inputMap json.RawMessage, proposalType string) (Proposal, error) {
	propStruct, ok := proposalRegistry[proposalType]
	if !ok {
		return nil, fmt.Errorf("%s is not a known proposal type", proposalType)
	}
	err := json.Unmarshal(inputMap, &propStruct)
	if err != nil {
		return nil, err
	}
	return propStruct, nil
}
