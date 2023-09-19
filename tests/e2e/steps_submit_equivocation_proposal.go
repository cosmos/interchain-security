package main

import "time"

// submits an invalid equivocation proposal which should be rejected
func stepsRejectEquivocationProposal(consumerName string, propNumber uint) []Step {
	return []Step{
		{
			// bob submits a proposal to slash himself
			Action: submitEquivocationProposalAction{
				Chain:     ChainID("consu"),
				From:      ValidatorID("bob"),
				Deposit:   10000001,
				Height:    10,
				Time:      time.Now(),
				Power:     500,
				Validator: ValidatorID("bob"),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495,
					},
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("bob"): 9500000000,
					},
					Proposals: &map[uint]Proposal{
						// proposal does not exist
						propNumber: TextProposal{},
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495,
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
			Action: submitEquivocationProposalAction{
				Chain:     ChainID("consu"),
				From:      ValidatorID("bob"),
				Deposit:   10000001,
				Height:    10,
				Time:      time.Now(), // not sure what time in equivocations means
				Power:     500,
				Validator: ValidatorID("bob"),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("bob"): 9489999999,
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
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
			},
		},
		{
			Action: voteGovProposalAction{
				Chain:      ChainID("provi"),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol")},
				Vote:       []string{"yes", "yes", "yes"},
				PropNumber: propNumber,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0, // bob is tombstoned after proposal passes
						ValidatorID("carol"): 0,
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
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500, // slash not reflected in consumer chain
						ValidatorID("carol"): 0,
					},
				},
			},
		},
		{
			// relay power change to consumer1
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0, // slash relayed to consumer chain
						ValidatorID("carol"): 0,
					},
				},
			},
		},
	}

	return s
}
