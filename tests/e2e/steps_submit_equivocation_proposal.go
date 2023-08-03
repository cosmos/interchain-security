package main

import "time"

// submits an invalid equivocation proposal which should be rejected
func stepsRejectEquivocationProposal(consumerName string, propNumber uint) []Step {
	return []Step{
		{
			// bob submits a proposal to slash himself
			action: submitEquivocationProposalAction{
				chain:     chainID("consu"),
				from:      validatorID("bob"),
				deposit:   10000001,
				height:    10,
				time:      time.Now(),
				power:     500,
				validator: validatorID("bob"),
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
					ValBalances: &map[validatorID]uint{
						validatorID("bob"): 9500000000,
					},
					Proposals: &map[uint]Proposal{
						// proposal does not exist
						propNumber: TextProposal{},
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
	}
}

// submits an equivocation proposal, votes on it, and tomstones the equivocating validator
func stepsSubmitEquivocationProposal(consumerName string, propNumber uint) []Step {
	s := []Step{
		{
			// bob submits a proposal to slash himself
			action: submitEquivocationProposalAction{
				chain:     chainID("consu"),
				from:      validatorID("bob"),
				deposit:   10000001,
				height:    10,
				time:      time.Now(), // not sure what time in equivocations means
				power:     500,
				validator: validatorID("bob"),
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
					ValBalances: &map[validatorID]uint{
						validatorID("bob"): 9489999999,
					},
					Proposals: &map[uint]Proposal{
						propNumber: EquivocationProposal{
							Deposit:          10000001,
							Status:           "PROPOSAL_STATUS_VOTING_PERIOD",
							ConsensusAddress: "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
							Power:            500,
							Height:           10,
						},
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
			},
		},
		{
			action: voteGovProposalAction{
				chain:      chainID("provi"),
				from:       []validatorID{validatorID("alice"), validatorID("bob"), validatorID("carol")},
				vote:       []string{"yes", "yes", "yes"},
				propNumber: propNumber,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0, // bob is tombstoned after proposal passes
						validatorID("carol"): 0,
					},
					Proposals: &map[uint]Proposal{
						propNumber: EquivocationProposal{
							Deposit:          10000001,
							Status:           "PROPOSAL_STATUS_PASSED",
							ConsensusAddress: "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
							Power:            500,
							Height:           10,
						},
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // slash not reflected in consumer chain
						validatorID("carol"): 0,
					},
				},
			},
		},
		{
			// relay power change to consumer1
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0,
						validatorID("carol"): 0,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0, // slash relayed to consumer chain
						validatorID("carol"): 0,
					},
				},
			},
		},
	}

	return s
}
