package main

import (
	"encoding/json"
	"fmt"
	"reflect"
)

// stores a proposal as a raw json, together with its type
type ProposalAndType struct {
	RawProposal json.RawMessage
	Type        string
}

type (
	// to have a ChainState object that does not have the overridden Marshal/Unmarshal method
	ChainStateCopy ChainState

	// duplicated from the ChainState with a minor change to the Proposals field
	ChainStateWithProposalTypes struct {
		ChainStateCopy
		Proposals *map[uint]ProposalAndType // the only thing changed from the real ChainState
	}
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
	case "main.SubmitConsumerAdditionProposalAction":
		var a SubmitConsumerAdditionProposalAction
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
	case "main.SubmitTextProposalAction":
		var a SubmitTextProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.SubmitConsumerRemovalProposalAction":
		var a SubmitConsumerRemovalProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.SubmitParamChangeLegacyProposalAction":
		var a SubmitParamChangeLegacyProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.VoteGovProposalAction":
		var a VoteGovProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.StartConsumerChainAction":
		var a StartConsumerChainAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.AddChainToRelayerAction":
		var a AddChainToRelayerAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.AddIbcConnectionAction":
		var a AddIbcConnectionAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.AddIbcChannelAction":
		var a AddIbcChannelAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.TransferChannelCompleteAction":
		var a TransferChannelCompleteAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.UnjailValidatorAction":
		var a UnjailValidatorAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.AssignConsumerPubKeyAction":
		var a AssignConsumerPubKeyAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.DelegateTokensAction":
		var a DelegateTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.RelayPacketsAction":
		var a RelayPacketsAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.RegisterRepresentativeAction":
		var a RegisterRepresentativeAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.RelayRewardPacketsToProviderAction":
		var a RelayRewardPacketsToProviderAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.SubmitChangeRewardDenomsProposalAction":
		var a SubmitChangeRewardDenomsProposalAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.DowntimeSlashAction":
		var a DowntimeSlashAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.UnbondTokensAction":
		var a UnbondTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.CancelUnbondTokensAction":
		var a CancelUnbondTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.RedelegateTokensAction":
		var a RedelegateTokensAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.DoublesignSlashAction":
		var a DoublesignSlashAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.StartRelayerAction":
		var a StartRelayerAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.SlashMeterReplenishmentAction":
		var a SlashMeterReplenishmentAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.WaitTimeAction":
		var a WaitTimeAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.CreateIbcClientsAction":
		var a CreateIbcClientsAction
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
	case "main.WaitUntilBlockAction":
		var a WaitUntilBlockAction
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
	case "main.LightClientEquivocationAttackAction":
		var a LightClientEquivocationAttackAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.LightClientAmnesiaAttackAction":
		var a LightClientAmnesiaAttackAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.LightClientLunaticAttackAction":
		var a LightClientLunaticAttackAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.ForkConsumerChainAction":
		var a ForkConsumerChainAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.StartConsumerEvidenceDetectorAction":
		var a StartConsumerEvidenceDetectorAction
		err := json.Unmarshal(rawAction, &a)
		if err == nil {
			return a, nil
		}
	case "main.UpdateLightClientAction":
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

// custom marshal and unmarshal functions for the chainstate that convert proposals to/from the auxiliary type with type info

// MarshalJSON transforms the ChainState into a ChainStateWithProposalTypes by adding type info to the proposals
func (c ChainState) MarshalJSON() ([]byte, error) {
	chainStateCopy := ChainStateCopy(c)
	chainStateWithProposalTypes := ChainStateWithProposalTypes{chainStateCopy, nil}
	if c.Proposals != nil {
		proposalsWithTypes := make(map[uint]ProposalAndType)
		for k, v := range *c.Proposals {
			rawMessage, err := json.Marshal(v)
			if err != nil {
				return nil, err
			}
			proposalsWithTypes[k] = ProposalAndType{rawMessage, reflect.TypeOf(v).String()}
		}
		chainStateWithProposalTypes.Proposals = &proposalsWithTypes
	}
	return json.Marshal(chainStateWithProposalTypes)
}

// UnmarshalJSON unmarshals the ChainStateWithProposalTypes into a ChainState by removing the type info from the proposals and getting back standard proposals
func (c *ChainState) UnmarshalJSON(data []byte) error {
	chainStateWithProposalTypes := ChainStateWithProposalTypes{}
	err := json.Unmarshal(data, &chainStateWithProposalTypes)
	if err != nil {
		return err
	}

	chainState := ChainState(chainStateWithProposalTypes.ChainStateCopy)
	*c = chainState

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
