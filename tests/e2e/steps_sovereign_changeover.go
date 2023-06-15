package main

import clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"

func stepsSovereignTransferChan() []Step {
	return []Step{
		{
			action: createIbcClientsAction{
				chainA: chainID("sover"),
				chainB: chainID("provi"),
			},
			state: State{},
		},
		{
			action: addIbcChannelAction{
				chainA:      chainID("sover"),
				chainB:      chainID("provi"),
				connectionA: 0,
				portA:       "transfer",
				portB:       "transfer",
				order:       "unordered",
				version:     "ics20-1",
			},
			state: State{},
		},
	}
}

// steps to convert sovereign to consumer chain
func stepsChangeoverToConsumer(consumerName string) []Step {
	s := []Step{
		{
			action: submitConsumerAdditionProposalAction{
				preCCV:              true,
				chain:               chainID("provi"),
				from:                validatorID("alice"),
				deposit:             10000001,
				consumerChain:       chainID(consumerName),
				distributionChannel: "channel-0", // consumer's channel end
				spawnTime:           0,
				initialHeight:       clienttypes.Height{RevisionNumber: 0, RevisionHeight: 111}, // 1 block after upgrade !important
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
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 111},
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
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 111},
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
				genesisChanges: ".app_state.ccvconsumer.params.soft_opt_out_threshold = \"0.05\"",
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
				clientA: 1,
				clientB: 1,
			},
			state: State{},
		},
		{
			action: addIbcChannelAction{
				chainA:      chainID(consumerName),
				chainB:      chainID("provi"),
				connectionA: 1,
				portA:       "consumer",
				portB:       "provider",
				order:       "ordered",
			},
			state: State{},
		},
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
	}
}

// TODO: use args instead of hardcoding
func stepsUpgradeChain() []Step {
	return []Step{
		{
			action: UpgradeProposalAction{
				chainID:       chainID("sover"),
				upgradeTitle:  "sovereign-changeover",
				proposer:      validatorID("alice"),
				upgradeHeight: 110,
			},
			state: State{
				chainID("sover"): ChainState{
					Proposals: &map[uint]Proposal{
						1: UpgradeProposal{
							Title:         "sovereign-changeover",
							UpgradeHeight: 110,
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
							UpgradeHeight: 110,
							Title:         "sovereign-changeover",
							Type:          "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal",
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
				},
			},
		},
		{
			action: waitUntilBlockAction{
				chain: chainID("sover"),
				block: 110,
			},
			state: State{},
		},
	}
}

// stepsPostChangeoverDelegate tests basic delegation and resulting validator power changes
func stepsPostChangeoverDelegate(consumerName string) []Step {
	return []Step{
		{
			action: SendTokensAction{
				chain:  chainID(consumerName),
				from:   validatorID("alice"),
				to:     validatorID("bob"),
				amount: 100,
			},
			state: State{
				chainID(consumerName): ChainState{
					// Tx should not go through, ICS channel is not setup until first VSC packet has been relayed to consumer
					ValBalances: &map[validatorID]uint{
						validatorID("bob"): 0,
					},
				},
			},
		},
		{
			action: delegateTokensAction{
				chain:  chainID("provi"),
				from:   validatorID("alice"),
				to:     validatorID("alice"),
				amount: 11000000,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 1,
			},
			state: State{
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			action: SendTokensAction{
				chain:  chainID(consumerName),
				from:   validatorID("alice"),
				to:     validatorID("bob"),
				amount: 100,
			},
			state: State{
				chainID(consumerName): ChainState{
					// Tx should go through, ICS channel is setup
					ValBalances: &map[validatorID]uint{
						validatorID("bob"): 100,
					},
				},
			},
		},
		{
			action: unbondTokensAction{
				chain:      chainID("provi"),
				unbondFrom: validatorID("alice"),
				sender:     validatorID("alice"),
				amount:     1000000,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						// Voting power on consumer should not be affected yet
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 1,
			},
			state: State{
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
	}
}
