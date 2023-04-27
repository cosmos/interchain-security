package main

import (
	"encoding/json"
	"fmt"
	"reflect"
)

type ProposalWithType struct {
	ProposalType string
	Proposal     Proposal
}

// MarshalJSON marshals a chainState into JSON while including the type of the proposal.
func (chainState ChainState) MarshalJSON() ([]byte, error) {
	var proposalsWithTypes map[uint]ProposalWithType
	if chainState.Proposals != nil {
		proposalsWithTypes = make(map[uint]ProposalWithType, len(*chainState.Proposals))

		for k, v := range *chainState.Proposals {
			proposalsWithTypes[k] = ProposalWithType{
				ProposalType: reflect.TypeOf(v).String(),
				Proposal:     v,
			}
		}
	} else {
		proposalsWithTypes = nil
	}

	result := struct {
		ValBalances             *map[ValidatorID]uint
		Proposals               *map[uint]ProposalWithType
		ValPowers               *map[ValidatorID]uint
		RepresentativePowers    *map[ValidatorID]uint
		Params                  *[]Param
		Rewards                 *Rewards
		ConsumerChains          *map[ChainID]bool
		AssignedKeys            *map[ValidatorID]string
		ProviderKeys            *map[ValidatorID]string // validatorID: validator provider key
		ConsumerChainQueueSizes *map[ChainID]uint
		GlobalSlashQueueSize    *uint
	}{
		ValBalances:             chainState.ValBalances,
		Proposals:               &proposalsWithTypes,
		ValPowers:               chainState.ValPowers,
		RepresentativePowers:    chainState.RepresentativePowers,
		Params:                  chainState.Params,
		Rewards:                 chainState.Rewards,
		ConsumerChains:          chainState.ConsumerChains,
		AssignedKeys:            chainState.AssignedKeys,
		ProviderKeys:            chainState.ProviderKeys,
		ConsumerChainQueueSizes: chainState.ConsumerChainQueueSizes,
		GlobalSlashQueueSize:    chainState.GlobalSlashQueueSize,
	}

	return json.Marshal(result)
}

func (state *ChainState) UnmarshalJSON(data []byte) error {
	var tmp struct {
		ValBalances             *map[ValidatorID]uint
		Proposals               *map[uint]json.RawMessage
		ValPowers               *map[ValidatorID]uint
		RepresentativePowers    *map[ValidatorID]uint
		Params                  *[]Param
		Rewards                 *Rewards
		ConsumerChains          *map[ChainID]bool
		AssignedKeys            *map[ValidatorID]string
		ProviderKeys            *map[ValidatorID]string // validatorID: validator provider key
		ConsumerChainQueueSizes *map[ChainID]uint
		GlobalSlashQueueSize    *uint
	}

	err := json.Unmarshal(data, &tmp)
	if err != nil {
		return err
	}

	var proposals *map[uint]Proposal
	if tmp.Proposals != nil {
		proposals, err = UnmarshalProposals(*tmp.Proposals)
		if err != nil {
			return err
		}
	}

	state.Proposals = proposals

	state.ValBalances = tmp.ValBalances
	state.ValPowers = tmp.ValPowers
	state.RepresentativePowers = tmp.RepresentativePowers
	state.Params = tmp.Params
	state.Rewards = tmp.Rewards
	state.ConsumerChains = tmp.ConsumerChains
	state.AssignedKeys = tmp.AssignedKeys
	state.ProviderKeys = tmp.ProviderKeys
	state.ConsumerChainQueueSizes = tmp.ConsumerChainQueueSizes
	state.GlobalSlashQueueSize = tmp.GlobalSlashQueueSize

	return nil
}

func UnmarshalProposals(proposals map[uint]json.RawMessage) (*map[uint]Proposal, error) {
	result := make(map[uint]Proposal, len(proposals))

	for k, v := range proposals {
		var tmp struct {
			Proposal     json.RawMessage
			ProposalType string
		}

		if err := json.Unmarshal(v, &tmp); err != nil {
			return nil, err
		}

		proposal, err := UnmarshalMapToProposalType(tmp.Proposal, tmp.ProposalType)
		if err != nil {
			return nil, err
		}
		result[k] = proposal
	}

	return &result, nil
}

// UnmarshalMapToProposalType takes a JSON message and a proposal type and marshals into an object of the corresponding proposal.
func UnmarshalMapToProposalType(input json.RawMessage, proposalType string) (Proposal, error) {
	switch proposalType {
	case "main.ConsumerAdditionProposal":
		var proposal ConsumerAdditionProposal
		err := json.Unmarshal(input, &proposal)
		if err != nil {
			return nil, err
		}
		return proposal, nil
	case "main.ConsumerRemovalProposal":
		var proposal ConsumerRemovalProposal
		err := json.Unmarshal(input, &proposal)
		if err != nil {
			return nil, err
		}
		return proposal, nil
	case "main.EquivocationProposal":
		var proposal EquivocationProposal
		err := json.Unmarshal(input, &proposal)
		if err != nil {
			return nil, err
		}
		return proposal, nil

	case "main.TextProposal":
		var proposal TextProposal
		err := json.Unmarshal(input, &proposal)
		if err != nil {
			return nil, err
		}
		return proposal, nil
	default:
		return nil, fmt.Errorf("%s is not a known proposal type", proposalType)
	}
}
