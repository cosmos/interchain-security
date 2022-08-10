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
			chain: providerChainId,
			validators: []StartChainValidator{
				{id: 1, stake: 500000000, allocation: 10000000000},
				{id: 0, stake: 500000000, allocation: 10000000000},
				{id: 2, stake: 500000000, allocation: 10000000000},
			},
		},
		state: State{
			providerChainId: ChainState{
				ValBalances: &map[uint]uint{
					0: 9500000000,
					1: 9500000000,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  providerChainId,
			from:   0,
			to:     1,
			amount: 2,
		},
		state: State{
			providerChainId: ChainState{
				ValBalances: &map[uint]uint{
					0: 9499999998,
					1: 9500000002,
				},
			},
		},
	},
	{
		action: SubmitConsumerProposalAction{
			chain:         providerChainId,
			from:          0,
			deposit:       10000001,
			consumerChain: consumerChainId,
			spawnTime:     0,
			initialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
		},
		state: State{
			providerChainId: ChainState{
				ValBalances: &map[uint]uint{
					0: 9489999997,
					1: 9500000002,
				},
				Proposals: &map[uint]Proposal{
					1: ConsumerProposal{
						Deposit:       10000001,
						Chain:         consumerChainId,
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
			chain:      providerChainId,
			from:       []uint{0, 1, 2},
			vote:       []string{"yes", "yes", "yes"},
			propNumber: 1,
		},
		state: State{
			providerChainId: ChainState{
				Proposals: &map[uint]Proposal{
					1: ConsumerProposal{
						Deposit:       10000001,
						Chain:         consumerChainId,
						SpawnTime:     0,
						InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
						Status:        "PROPOSAL_STATUS_PASSED",
					},
				},
				ValBalances: &map[uint]uint{
					0: 9499999998,
					1: 9500000002,
				},
			},
		},
	},
	{
		action: StartConsumerChainAction{
			consumerChain: consumerChainId,
			providerChain: providerChainId,
			validators: []StartChainValidator{
				{id: 2, stake: 500000000, allocation: 10000000000},
				{id: 0, stake: 500000000, allocation: 10000000000},
				{id: 1, stake: 500000000, allocation: 10000000000},
			},
		},
		state: State{
			providerChainId: ChainState{
				ValBalances: &map[uint]uint{
					0: 9499999998,
					1: 9500000002,
				},
			},
			consumerChainId: ChainState{
				ValBalances: &map[uint]uint{
					0: 10000000000,
					1: 10000000000,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  consumerChainId,
			from:   0,
			to:     1,
			amount: 1,
		},
		state: State{
			consumerChainId: ChainState{
				// Tx on consumer chain should not go through before ICS channel is setup
				ValBalances: &map[uint]uint{
					0: 10000000000,
					1: 10000000000,
				},
			},
		},
	},
	{
		action: AddIbcConnectionAction{
			chainA:  consumerChainId,
			chainB:  providerChainId,
			clientA: 0,
			clientB: 0,
			order:   "ordered",
		},
		state: State{},
	},
	{
		action: AddIbcChannelAction{
			chainA:      consumerChainId,
			chainB:      providerChainId,
			connectionA: 0,
			portA:       "consumer",
			portB:       "provider",
			order:       "ordered",
		},
		state: State{},
	},
	{
		action: DelegateTokensAction{
			chain:  providerChainId,
			from:   0,
			to:     0,
			amount: 11000000,
		},
		state: State{
			providerChainId: ChainState{
				ValPowers: &map[uint]uint{
					0: 511,
					1: 500,
					2: 500,
				},
			},
			consumerChainId: ChainState{
				ValPowers: &map[uint]uint{
					0: 500,
					1: 500,
					2: 500,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  consumerChainId,
			from:   0,
			to:     1,
			amount: 1,
		},
		state: State{
			consumerChainId: ChainState{
				// Tx should not go through, ICS channel is not setup until first VSC packet has been relayed to consumer
				ValBalances: &map[uint]uint{
					0: 10000000000,
					1: 10000000000,
				},
			},
		},
	},
	{
		action: RelayPacketsAction{
			chain:   providerChainId,
			port:    "provider",
			channel: 0,
		},
		state: State{
			consumerChainId: ChainState{
				ValPowers: &map[uint]uint{
					0: 511,
					1: 500,
					2: 500,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  consumerChainId,
			from:   0,
			to:     1,
			amount: 1,
		},
		state: State{
			consumerChainId: ChainState{
				// Now tx should execute
				ValBalances: &map[uint]uint{
					0: 9999999999,
					1: 10000000001,
				},
			},
		},
	},
	{
		action: UnbondTokensAction{
			chain:      providerChainId,
			unbondFrom: 0,
			sender:     0,
			amount:     11000000,
		},
		state: State{
			providerChainId: ChainState{
				ValPowers: &map[uint]uint{
					0: 500,
					1: 500,
					2: 500,
				},
			},
			consumerChainId: ChainState{
				ValPowers: &map[uint]uint{
					// Voting power on consumer should not be affected yet
					0: 511,
					1: 500,
					2: 500,
				},
			},
		},
	},
	{
		action: RelayPacketsAction{
			chain:   providerChainId,
			port:    "provider",
			channel: 0,
		},
		state: State{
			consumerChainId: ChainState{
				ValPowers: &map[uint]uint{
					0: 500,
					1: 500,
					2: 500,
				},
			},
		},
	},
	// TODO: Test full unbonding functionality, considering liquidity after unbonding period, etc.
}
