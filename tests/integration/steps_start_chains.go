package main

import (
	"fmt"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
)

func stepStartProviderChain() []Step {
	return []Step{
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
	}
}

// startSovereignChain starts a sovereign chain not participating in ICS
// transfer channels will be setup with chains provided in ibcChains and
// stored inside "sover" chainConfig
func startSovereignChain(tr *TestRun, ibcChains []string) []Step {
	config := tr.chainConfigs[chainID("sover")]
	s := []Step{
		{
			action: StartChainAction{
				chain: chainID("sover"),
				validators: []StartChainValidator{
					{id: validatorID("bob"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("carol"), stake: 500000000, allocation: 10000000000},
				},
			},
			state: State{
				chainID("sover"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9500000000,
						validatorID("carol"): 9500000000,
					},
				},
			},
		},
	}

	m := map[chainID]string{}
	for i, chain := range ibcChains {
		m[chainID(chain)] = fmt.Sprintf("channel-%d", i)
		s = append(s,
			Step{
				action: addIbcConnectionAction{
					chainA:        chainID("sover"),
					chainB:        chainID(chain),
					createClients: true,
				},
				state: State{},
			},
			Step{
				action: addIbcChannelAction{
					chainA:      chainID("sover"),
					chainB:      chainID(chain),
					connectionA: uint(i),
					portA:       "transfer",
					portB:       "transfer",
					order:       "unordered",
					noVersion:   true,
				},
				state: State{},
			},
		)
	}
	config.transferChannels = m
	tr.chainConfigs[chainID("sover")] = config
	return s
}

func stepsStartConsumerChain(consumerName string, proposalIndex uint, setupTransferChan bool) []Step {
	s := []Step{
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
						proposalIndex: ConsumerProposal{
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
				propNumber: proposalIndex,
			},
			state: State{
				chainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						proposalIndex: ConsumerProposal{
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
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9500000000,
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

// starts provider and single consumer chain
// * genesisParams overrides consumer genesis params
// * setupTransferChan creates a transfer channel between provider and consumer
func stepsStartChains(consumerNames []string, setupTransferChan bool) []Step {
	s := stepStartProviderChain()
	for i, consumerName := range consumerNames {
		s = append(s, stepsStartConsumerChain(consumerName, uint(i+1), false)...)
	}

	return s
}
