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
			chain: provider,
			validators: []StartChainValidator{
				{id: bob, stake: 500000000, allocation: 10000000000},
				{id: alice, stake: 500000000, allocation: 10000000000},
				{id: carol, stake: 500000000, allocation: 10000000000},
			},
			genesisChanges: "", // No custom genesis changes for this action
			skipGentx:      false,
		},
		state: State{
			provider: ChainState{
				ValBalances: &map[validatorID]uint{
					alice: 9500000000,
					bob:   9500000000,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  provider,
			from:   alice,
			to:     bob,
			amount: 2,
		},
		state: State{
			provider: ChainState{
				ValBalances: &map[validatorID]uint{
					alice: 9499999998,
					bob:   9500000002,
				},
			},
		},
	},
	{
		action: SubmitConsumerProposalAction{
			chain:         provider,
			from:          alice,
			deposit:       10000001,
			consumerChain: consumer,
			spawnTime:     0,
			initialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
		},
		state: State{
			provider: ChainState{
				ValBalances: &map[validatorID]uint{
					alice: 9489999997,
					bob:   9500000002,
				},
				Proposals: &map[uint]Proposal{
					1: ConsumerProposal{
						Deposit:       10000001,
						Chain:         consumer,
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
			chain:      provider,
			from:       []validatorID{alice, bob, carol},
			vote:       []string{"yes", "yes", "yes"},
			propNumber: 1,
		},
		state: State{
			provider: ChainState{
				Proposals: &map[uint]Proposal{
					1: ConsumerProposal{
						Deposit:       10000001,
						Chain:         consumer,
						SpawnTime:     0,
						InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
						Status:        "PROPOSAL_STATUS_PASSED",
					},
				},
				ValBalances: &map[validatorID]uint{
					alice: 9499999998,
					bob:   9500000002,
				},
			},
		},
	},
	{
		action: StartConsumerChainAction{
			consumerChain: consumer,
			providerChain: provider,
			validators: []StartChainValidator{
				{id: carol, stake: 500000000, allocation: 10000000000},
				{id: alice, stake: 500000000, allocation: 10000000000},
				{id: bob, stake: 500000000, allocation: 10000000000},
			},
		},
		state: State{
			provider: ChainState{
				ValBalances: &map[validatorID]uint{
					alice: 9499999998,
					bob:   9500000002,
				},
			},
			consumer: ChainState{
				ValBalances: &map[validatorID]uint{
					alice: 10000000000,
					bob:   10000000000,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  consumer,
			from:   alice,
			to:     bob,
			amount: 1,
		},
		state: State{
			consumer: ChainState{
				// Tx on consumer chain should not go through before ICS channel is setup
				ValBalances: &map[validatorID]uint{
					alice: 10000000000,
					bob:   10000000000,
				},
			},
		},
	},
	{
		action: AddIbcConnectionAction{
			chainA:  consumer,
			chainB:  provider,
			clientA: 0,
			clientB: 0,
			order:   "ordered",
		},
		state: State{},
	},
	{
		action: AddIbcChannelAction{
			chainA:      consumer,
			chainB:      provider,
			connectionA: 0,
			portA:       "consumer",
			portB:       "provider",
			order:       "ordered",
		},
		state: State{},
	},
	{
		action: DelegateTokensAction{
			chain:  provider,
			from:   alice,
			to:     alice,
			amount: 11000000,
		},
		state: State{
			provider: ChainState{
				ValPowers: &map[validatorID]uint{
					alice: 511,
					bob:   500,
					carol: 500,
				},
			},
			consumer: ChainState{
				ValPowers: &map[validatorID]uint{
					alice: 500,
					bob:   500,
					carol: 500,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  consumer,
			from:   alice,
			to:     bob,
			amount: 1,
		},
		state: State{
			consumer: ChainState{
				// Tx should not go through, ICS channel is not setup until first VSC packet has been relayed to consumer
				ValBalances: &map[validatorID]uint{
					alice: 10000000000,
					bob:   10000000000,
				},
			},
		},
	},
	{
		action: RelayPacketsAction{
			chain:   provider,
			port:    "provider",
			channel: 0,
		},
		state: State{
			consumer: ChainState{
				ValPowers: &map[validatorID]uint{
					alice: 511,
					bob:   500,
					carol: 500,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  consumer,
			from:   alice,
			to:     bob,
			amount: 1,
		},
		state: State{
			consumer: ChainState{
				// Now tx should execute
				ValBalances: &map[validatorID]uint{
					alice: 9999999999,
					bob:   10000000001,
				},
			},
		},
	},
	{
		action: UnbondTokensAction{
			chain:      provider,
			unbondFrom: alice,
			sender:     alice,
			amount:     11000000,
		},
		state: State{
			provider: ChainState{
				ValPowers: &map[validatorID]uint{
					alice: 500,
					bob:   500,
					carol: 500,
				},
			},
			consumer: ChainState{
				ValPowers: &map[validatorID]uint{
					// Voting power on consumer should not be affected yet
					alice: 511,
					bob:   500,
					carol: 500,
				},
			},
		},
	},
	{
		action: RelayPacketsAction{
			chain:   provider,
			port:    "provider",
			channel: 0,
		},
		state: State{
			consumer: ChainState{
				ValPowers: &map[validatorID]uint{
					alice: 500,
					bob:   500,
					carol: 500,
				},
			},
		},
	},
	// TODO: Test full unbonding functionality, considering liquidity after unbonding period, etc.
}
