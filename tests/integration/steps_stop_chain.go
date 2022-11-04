package main

// submits a consumer-removal proposal and removes the chain
func stepsStopChain(consumerName string) []Step {
	s := []Step{
		{
			action: submitConsumerRemovalProposalAction{
				chain:         chainID("provi"),
				from:          validatorID("alice"),
				deposit:       10000001,
				consumerChain: chainID(consumerName),
				stopTime:      0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9479013472, // was 9489999997
						validatorID("bob"):   9500000002,
					},
					Proposals: &map[uint]Proposal{
						2: ConsumerRemovalProposal{
							Deposit:  10000001,
							Chain:    chainID(consumerName),
							StopTime: 0,
							Status:   "PROPOSAL_STATUS_VOTING_PERIOD",
						},
					},
				},
			},
		},
		{
			action: voteGovProposalAction{
				chain:      chainID("provi"),
				from:       []validatorID{validatorID("alice"), validatorID("bob"), validatorID("carol")},
				vote:       []string{"yes", "yes", "yes"},
				propNumber: 2,
			},
			state: State{
				chainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						2: ConsumerRemovalProposal{
							Deposit:  10000001,
							Chain:    chainID(consumerName),
							StopTime: 0,
							Status:   "PROPOSAL_STATUS_PASSED",
						},
					},
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9479013472,
						validatorID("bob"):   9500000002,
					},
				},
			},
		},
		{
			action: queryConsumerChainRemovedAction{
				providerChain: chainID("provi"),
				consumerChain: chainID(consumerName),
			},
			state: State{},
		},
	}

	return s
}
