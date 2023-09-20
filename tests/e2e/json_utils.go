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

// UnmarshalMapToActionType takes a JSON object and an action type and marshals into an object of the corresponding action.
func UnmarshalMapToActionType(rawAction json.RawMessage, actionTypeString string) (interface{}, error) {
	var err error
	switch actionTypeString {
	case "main.submitConsumerAdditionProposalAction":
		var a submitConsumerAdditionProposalAction
		err = json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.SendTokensAction":
		var a SendTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.StartChainAction":
		var a StartChainAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.submitTextProposalAction":
		var a submitTextProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.submitConsumerRemovalProposalAction":
		var a submitConsumerRemovalProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.submitEquivocationProposalAction":
		var a submitEquivocationProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.submitParamChangeLegacyProposalAction":
		var a submitParamChangeLegacyProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.voteGovProposalAction":
		var a voteGovProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.startConsumerChainAction":
		var a startConsumerChainAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.addChainToRelayerAction":
		var a addChainToRelayerAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.addIbcConnectionAction":
		var a addIbcConnectionAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.addIbcChannelAction":
		var a addIbcChannelAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.transferChannelCompleteAction":
		var a transferChannelCompleteAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.unjailValidatorAction":
		var a unjailValidatorAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.assignConsumerPubKeyAction":
		var a assignConsumerPubKeyAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.delegateTokensAction":
		var a delegateTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.relayPacketsAction":
		var a relayPacketsAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.registerRepresentativeAction":
		var a registerRepresentativeAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.relayRewardPacketsToProviderAction":
		var a relayRewardPacketsToProviderAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.submitChangeRewardDenomsProposalAction":
		var a submitChangeRewardDenomsProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.downtimeSlashAction":
		var a downtimeSlashAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.unbondTokensAction":
		var a unbondTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.cancelUnbondTokensAction":
		var a cancelUnbondTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.redelegateTokensAction":
		var a redelegateTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.doublesignSlashAction":
		var a doublesignSlashAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.startRelayerAction":
		var a startRelayerAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.slashThrottleDequeueAction":
		var a slashThrottleDequeueAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.createIbcClientsAction":
		var a createIbcClientsAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.LegacyUpgradeProposalAction":
		var a LegacyUpgradeProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.waitUntilBlockAction":
		var a waitUntilBlockAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.ChangeoverChainAction":
		var a ChangeoverChainAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.StartSovereignChainAction":
		var a StartSovereignChainAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.lightClientEquivocationAttackAction":
		var a lightClientEquivocationAttackAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.lightClientAmnesiaAttackAction":
		var a lightClientAmnesiaAttackAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.lightClientLunaticAttackAction":
		var a lightClientLunaticAttackAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	default:
		return nil, fmt.Errorf("unknown action type: %s", actionTypeString)
	}
	return nil, err
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

// UnmarshalProposalWithType takes a JSON object and a proposal type and marshals into an object of the corresponding proposal.
func UnmarshalProposalWithType(inputMap json.RawMessage, proposalType string) (Proposal, error) {
	var err error
	switch proposalType {
	case "main.TextProposal":
		prop := TextProposal{}
		err := json.Unmarshal(inputMap, &prop)
		if err == nil {
			return prop, nil
		}
	case "main.ConsumerAdditionProposal":
		prop := ConsumerAdditionProposal{}
		err := json.Unmarshal(inputMap, &prop)
		if err == nil {
			return prop, nil
		}
	case "main.UpgradeProposal":
		prop := UpgradeProposal{}
		err := json.Unmarshal(inputMap, &prop)
		if err == nil {
			return prop, nil
		}
	case "main.ConsumerRemovalProposal":
		prop := ConsumerRemovalProposal{}
		err := json.Unmarshal(inputMap, &prop)
		if err == nil {
			return prop, nil
		}
	case "main.EquivocationProposal":
		prop := EquivocationProposal{}
		err := json.Unmarshal(inputMap, &prop)
		if err == nil {
			return prop, nil
		}
	case "main.ParamsProposal":
		prop := ParamsProposal{}
		err := json.Unmarshal(inputMap, &prop)
		if err == nil {
			return prop, nil
		}
	default:
		return nil, fmt.Errorf("%s is not a known proposal type", proposalType)
	}

	return nil, err
}
