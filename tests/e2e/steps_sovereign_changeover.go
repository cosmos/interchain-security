package main

import clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"

func stepsChangeoverToConsumer(consumerName string, setupTransferChans bool) []Step {
	s := []Step{
		{
			action: StartChainAction{
				chain: chainID("provi"),
				validators: []StartChainValidator{
					{id: validatorID("bob"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("carol"), stake: 500000000, allocation: 10000000000},
				},
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9500000000,
						validatorID("carol"): 9500000000,
					},
				},
			},
		},
		{
			action: submitConsumerAdditionProposalAction{
				chain:         chainID("provi"),
				from:          validatorID("alice"),
				deposit:       10000001,
				consumerChain: chainID(consumerName),
				spawnTime:     0,
				initialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9489999999,
						validatorID("bob"):   9500000000,
					},
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         chainID(consumerName),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
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
				propNumber: 1,
			},
			state: State{
				chainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         chainID(consumerName),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9500000000,
					},
				},
			},
		},
		{
			action: ChangeoverChainAction{
				sovereignChain: chainID(consumerName),
				providerChain:  chainID("provi"),
				validators: []StartChainValidator{
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("bob"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("carol"), stake: 500000000, allocation: 10000000000},
				},
				// For consumers that're launching with the provider being on an earlier version
				// of ICS before the soft opt-out threshold was introduced, we need to set the
				// soft opt-out threshold to 0.05 in the consumer genesis to ensure that the
				// consumer binary doesn't panic. Sdk requires that all params are set to valid
				// values from the genesis file.
				genesisChanges: ".app_state.ccvconsumer.params.soft_opt_out_threshold = \"0.05\" | " +
					".app_state.ccvconsumer.params.pre_ccv = true",
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						// uses val powers from consumer
						validatorID("alice"): 500,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			action: addIbcConnectionAction{
				chainA:  chainID(consumerName),
				chainB:  chainID("provi"),
				clientA: 0,
				clientB: 0,
			},
			state: State{},
		},
		{
			action: addIbcChannelAction{
				chainA:      chainID(consumerName),
				chainB:      chainID("provi"),
				connectionA: 0,
				portA:       "consumer",
				portB:       "provider",
				order:       "ordered",
			},
			state: State{},
		},
	}

	// currently only used in democracy tests
	if setupTransferChans {
		s = append(s, Step{
			action: transferChannelCompleteAction{
				chainA:      chainID(consumerName),
				chainB:      chainID("provi"),
				connectionA: 0,
				portA:       "transfer",
				portB:       "transfer",
				order:       "unordered",
				channelA:    1,
				channelB:    1,
			},
			state: State{},
		})
	}
	return s
}

// start sovereign chain with 2 validators
// nodes will cease being validators once the changeover occurs
func stepRunSovereignChain() []Step {
	return []Step{
		{
			action: StartSovereignChainAction{
				chain: chainID("sover"),
				validators: []StartChainValidator{
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
				},
			},
			state: State{
				chainID("sover"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
					},
				},
			},
		},
		{
			action: delegateTokensAction{
				chain:  chainID("sover"),
				from:   validatorID("alice"),
				to:     validatorID("alice"),
				amount: 11000000,
			},
			state: State{
				chainID("sover"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   0, // does not exist on pre-ccv sover
						validatorID("carol"): 0, // does not exist on pre-ccv sover
					},
				},
			},
		},
		{
			action: UpgradeProposalAction{
				chainID:       chainID("sover"),
				upgradeTitle:  "sovereign-changeover",
				proposer:      validatorID("alice"),
				upgradeHeight: 50,
			},
			state: State{
				chainID("sover"): ChainState{
					Proposals: &map[uint]Proposal{
						1: UpgradeProposal{
							Title:         "sovereign-changeover",
							UpgradeHeight: 50,
							Type:          "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal",
							Deposit:       10000000,
							Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
						},
					},
				},
			},
		},
		{
			action: voteGovProposalAction{
				chain:      chainID("sover"),
				from:       []validatorID{validatorID("alice")},
				vote:       []string{"yes"},
				propNumber: 1,
			},
			state: State{
				chainID("sover"): ChainState{
					Proposals: &map[uint]Proposal{
						1: UpgradeProposal{
							Deposit:       10000000,
							UpgradeHeight: 50,
							Title:         "sovereign-changeover",
							Type:          "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal",
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
				},
			},
		},
	}
}
