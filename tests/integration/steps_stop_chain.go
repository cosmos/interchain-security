package main

// submits a consumer-removal proposal and removes the chain
func stepsStopChain(consumerName string) []Step {
	s := []Step{
		{
			action: submitConsumerRemovalProposalAction{
				chain:          chainID("provi"),
				from:           validatorID("bob"),
				deposit:        10000001,
				consumerChain:  chainID(consumerName),
				stopTimeOffset: 0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("bob"): 9490000001,
					},
					Proposals: &map[uint]Proposal{
						2: ConsumerRemovalProposal{
							Deposit:  10000001,
							Chain:    chainID(consumerName),
							StopTime: 0,
							Status:   "PROPOSAL_STATUS_VOTING_PERIOD",
						},
					},
					ConsumerChains: &map[chainID]bool{"consu": true},
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
						validatorID("bob"): 9500000002,
					},
					ConsumerChains: &map[chainID]bool{},
				},
			},
		},
	}

	return s
}
