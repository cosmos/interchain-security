package main

import "time"

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
						validatorID("carol"): 495,
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
						validatorID("carol"): 495,
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
						validatorID("bob"):   0, // bob is slashed after proposal passes
						validatorID("carol"): 495,
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
						validatorID("carol"): 495,
					},
				},
			},
		},
		{
			// relay power change to consumer1
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0,
						validatorID("carol"): 495,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0, // slash relayed to consumer chain
						validatorID("carol"): 495,
					},
				},
			},
		},
	}

	return s
}
