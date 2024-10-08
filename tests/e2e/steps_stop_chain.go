package main

import (
	gov "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
)

// start relayer so that all messages are relayed
func stepsStartRelayer() []Step {
	return []Step{
		{
			Action: StartRelayerAction{},
			State:  State{},
		},
	}
}

// submits a consumer-removal proposal and removes the chain
func stepsStopChain(consumerName string, propNumber uint) []Step {
	s := []Step{
		{
			Action: SubmitConsumerRemovalProposalAction{
				Chain:         ChainID("provi"),
				From:          ValidatorID("bob"),
				Deposit:       10000001,
				ConsumerChain: ChainID(consumerName),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("bob"): 9489999999,
					},
					Proposals: &map[uint]Proposal{
						propNumber: ConsumerRemovalProposal{
							Deposit: 10000001,
							Chain:   ChainID(consumerName),
							Status:  gov.ProposalStatus_PROPOSAL_STATUS_VOTING_PERIOD.String(),
						},
					},
					ConsumerChains: &map[ChainID]bool{"consu": true}, // consumer chain not yet removed
				},
			},
		},
		{
			Action: VoteGovProposalAction{
				Chain:      ChainID("provi"),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol")},
				Vote:       []string{"yes", "yes", "yes"},
				PropNumber: propNumber,
			},
			State: State{
				ChainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						propNumber: ConsumerRemovalProposal{
							Deposit: 10000001,
							Chain:   ChainID(consumerName),
							Status:  gov.ProposalStatus_PROPOSAL_STATUS_PASSED.String(),
						},
					},
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("bob"): 9500000000,
					},
					ConsumerChains: &map[ChainID]bool{}, // Consumer chain is now removed
				},
			},
		},
	}

	return s
}

// submits a consumer-removal proposal and votes no on it
// the chain should not be removed
func stepsConsumerRemovalPropNotPassing(consumerName string, propNumber uint) []Step {
	s := []Step{
		{
			Action: SubmitConsumerRemovalProposalAction{
				Chain:         ChainID("provi"),
				From:          ValidatorID("bob"),
				Deposit:       10000001,
				ConsumerChain: ChainID(consumerName),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("bob"): 9489999999,
					},
					Proposals: &map[uint]Proposal{
						propNumber: ConsumerRemovalProposal{
							Deposit: 10000001,
							Chain:   ChainID(consumerName),
							Status:  gov.ProposalStatus_PROPOSAL_STATUS_VOTING_PERIOD.String(),
						},
					},
					ConsumerChains: &map[ChainID]bool{"consu": true}, // consumer chain not removed
				},
			},
		},
		{
			Action: VoteGovProposalAction{
				Chain:      ChainID("provi"),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol")},
				Vote:       []string{"no", "no", "no"},
				PropNumber: propNumber,
			},
			State: State{
				ChainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						propNumber: ConsumerRemovalProposal{
							Deposit: 10000001,
							Chain:   ChainID(consumerName),
							Status:  gov.ProposalStatus_PROPOSAL_STATUS_REJECTED.String(),
						},
					},
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("bob"): 9500000000,
					},
					ConsumerChains: &map[ChainID]bool{"consu": true}, // consumer chain not removed
				},
			},
		},
	}

	return s
}
