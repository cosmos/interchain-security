package main

import (
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
)

// starts provider and single consumer chain
// * genesisParams overrides consumer genesis params
// * setupTransferChan creates a transfer channel between provider and consumer
func stepsStartChains(consumerName string, setupTransferChan bool) []Step {
	s := []Step{
		{
			action: StartChainAction{
				chain: chainID("provi"),
				validators: []StartChainValidator{
					{id: validatorID("bob"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("carol"), stake: 500000000, allocation: 10000000000},
				},
				genesisChanges: "", // No custom genesis changes for this action
				skipGentx:      false,
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9500000000,
					},
				},
			},
		},
		{
			action: SendTokensAction{
				chain:  chainID("provi"),
				from:   validatorID("alice"),
				to:     validatorID("bob"),
				amount: 2,
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9499999998,
						validatorID("bob"):   9500000002,
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
						validatorID("alice"): 9489999997,
						validatorID("bob"):   9500000002,
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
						validatorID("alice"): 9499999998,
						validatorID("bob"):   9500000002,
					},
				},
			},
		},
		{
			action: startConsumerChainAction{
				consumerChain: chainID(consumerName),
				providerChain: chainID("provi"),
				// genesisChanges: consumerGenesisParams,
				validators: []StartChainValidator{
					{id: validatorID("carol"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("bob"), stake: 500000000, allocation: 10000000000},
				},
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9499999998,
						validatorID("bob"):   9500000002,
					},
				},
				chainID(consumerName): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 10000000000,
						validatorID("bob"):   10000000000,
					},
				},
			},
		},
		{
			action: SendTokensAction{
				chain:  chainID(consumerName),
				from:   validatorID("alice"),
				to:     validatorID("bob"),
				amount: 1,
			},
			state: State{
				chainID(consumerName): ChainState{
					// Tx on consumer chain should not go through before ICS channel is setup
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 10000000000,
						validatorID("bob"):   10000000000,
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
				order:   "ordered",
			},
			state: State{},
		},
		{
			action: addIbcChannelAction{
				chainA:      chainID(consumerName),
				chainB:      chainID("provi"),
				connectionA: 0,
				portA:       "consumer", // TODO: check port mapping
				portB:       "provider",
				order:       "ordered",
			},
			state: State{},
		},
	}

	// currently only used in democracy tests
	if setupTransferChan {
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
