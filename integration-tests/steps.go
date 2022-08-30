package main

import (
	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
)

type Step struct {
	action interface{}
	state  State
}

var happyPathSteps = []Step{
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
		action: SubmitConsumerProposalAction{
			chain:         chainID("provi"),
			from:          validatorID("alice"),
			deposit:       10000001,
			consumerChain: chainID("consu"),
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
					1: ConsumerProposal{
						Deposit:       10000001,
						Chain:         chainID("consu"),
						SpawnTime:     0,
						InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
						Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
					},
				},
			},
		},
	},
	{
		action: VoteGovProposalAction{
			chain:      chainID("provi"),
			from:       []validatorID{validatorID("alice"), validatorID("bob"), validatorID("carol")},
			vote:       []string{"yes", "yes", "yes"},
			propNumber: 1,
		},
		state: State{
			chainID("provi"): ChainState{
				Proposals: &map[uint]Proposal{
					1: ConsumerProposal{
						Deposit:       10000001,
						Chain:         chainID("consu"),
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
		action: StartConsumerChainAction{
			consumerChain: chainID("consu"),
			providerChain: chainID("provi"),
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
			chainID("consu"): ChainState{
				ValBalances: &map[validatorID]uint{
					validatorID("alice"): 10000000000,
					validatorID("bob"):   10000000000,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  chainID("consu"),
			from:   validatorID("alice"),
			to:     validatorID("bob"),
			amount: 1,
		},
		state: State{
			chainID("consu"): ChainState{
				// Tx on consumer chain should not go through before ICS channel is setup
				ValBalances: &map[validatorID]uint{
					validatorID("alice"): 10000000000,
					validatorID("bob"):   10000000000,
				},
			},
		},
	},
	{
		action: AddIbcConnectionAction{
			chainA:  chainID("consu"),
			chainB:  chainID("provi"),
			clientA: 0,
			clientB: 0,
			order:   "ordered",
		},
		state: State{},
	},
	{
		action: AddIbcChannelAction{
			chainA:      chainID("consu"),
			chainB:      chainID("provi"),
			connectionA: 0,
			portA:       "consumer",
			portB:       "provider",
			order:       "ordered",
		},
		state: State{},
	},
	{
		action: DelegateTokensAction{
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
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 500,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  chainID("consu"),
			from:   validatorID("alice"),
			to:     validatorID("bob"),
			amount: 1,
		},
		state: State{
			chainID("consu"): ChainState{
				// Tx should not go through, ICS channel is not setup until first VSC packet has been relayed to consumer
				ValBalances: &map[validatorID]uint{
					validatorID("alice"): 10000000000,
					validatorID("bob"):   10000000000,
				},
			},
		},
	},
	{
		action: RelayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("consu"): ChainState{
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
			chain:  chainID("consu"),
			from:   validatorID("alice"),
			to:     validatorID("bob"),
			amount: 1,
		},
		state: State{
			chainID("consu"): ChainState{
				// Now tx should execute
				ValBalances: &map[validatorID]uint{
					validatorID("alice"): 9999999999,
					validatorID("bob"):   10000000001,
				},
			},
		},
	},
	{
		action: UnbondTokensAction{
			chain:      chainID("provi"),
			unbondFrom: validatorID("alice"),
			sender:     validatorID("alice"),
			amount:     11000000,
		},
		state: State{
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 500,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
			},
			chainID("consu"): ChainState{
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
		action: RelayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 500,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
			},
		},
	},
	{
		action: RedelegateTokensAction{
			chain:    chainID("provi"),
			src:      validatorID("bob"),
			dst:      validatorID("carol"),
			txSender: validatorID("bob"),
			amount:   11000000,
		},
		state: State{
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 500,
					validatorID("bob"):   489,
					validatorID("carol"): 511,
				},
			},
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					// Voting power changes not seen by consumer yet
					validatorID("alice"): 500,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
			},
		},
	},
	{
		action: RelayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					// Now power changes are seen by consumer
					validatorID("alice"): 500,
					validatorID("bob"):   489,
					validatorID("carol"): 511,
				},
			},
		},
	},

	// TODO: Test full unbonding functionality, tracked as: https://github.com/cosmos/interchain-security/issues/311
}
