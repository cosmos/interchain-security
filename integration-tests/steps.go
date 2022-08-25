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
				{id: validatorBob, stake: 500000000, allocation: 10000000000},
				{id: validatorAlice, stake: 500000000, allocation: 10000000000},
				{id: validatorCarol, stake: 500000000, allocation: 10000000000},
			},
		},
		state: State{
			providerChainId: ChainState{
				ValBalances: &map[string]uint{
					validatorAlice: 9500000000,
					validatorBob:   9500000000,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  providerChainId,
			from:   validatorAlice,
			to:     validatorBob,
			amount: 2,
		},
		state: State{
			providerChainId: ChainState{
				ValBalances: &map[string]uint{
					validatorAlice: 9499999998,
					validatorBob:   9500000002,
				},
			},
		},
	},
	{
		action: SubmitConsumerProposalAction{
			chain:         providerChainId,
			from:          validatorAlice,
			deposit:       10000001,
			consumerChain: consumerChainId,
			spawnTime:     0,
			initialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
		},
		state: State{
			providerChainId: ChainState{
				ValBalances: &map[string]uint{
					validatorAlice: 9489999997,
					validatorBob:   9500000002,
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
			from:       []string{validatorAlice, validatorBob, validatorCarol},
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
				ValBalances: &map[string]uint{
					validatorBob:   9499999998,
					validatorAlice: 9500000002,
				},
			},
		},
	},
	{
		action: StartConsumerChainAction{
			consumerChain: consumerChainId,
			providerChain: providerChainId,
			validators: []StartChainValidator{
				{id: validatorCarol, stake: 500000000, allocation: 10000000000},
				{id: validatorAlice, stake: 500000000, allocation: 10000000000},
				{id: validatorBob, stake: 500000000, allocation: 10000000000},
			},
		},
		state: State{
			providerChainId: ChainState{
				ValBalances: &map[string]uint{
					validatorAlice: 9499999998,
					validatorBob:   9500000002,
				},
			},
			consumerChainId: ChainState{
				ValBalances: &map[string]uint{
					validatorAlice: 10000000000,
					validatorBob:   10000000000,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  consumerChainId,
			from:   validatorAlice,
			to:     validatorBob,
			amount: 1,
		},
		state: State{
			consumerChainId: ChainState{
				// Tx on consumer chain should not go through before ICS channel is setup
				ValBalances: &map[string]uint{
					validatorAlice: 10000000000,
					validatorBob:   10000000000,
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
			from:   validatorAlice,
			to:     validatorAlice,
			amount: 11000000,
		},
		state: State{
			providerChainId: ChainState{
				ValPowers: &map[string]uint{
					validatorAlice: 511,
					validatorBob:   500,
					validatorCarol: 500,
				},
			},
			consumerChainId: ChainState{
				ValPowers: &map[string]uint{
					validatorAlice: 500,
					validatorBob:   500,
					validatorCarol: 500,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  consumerChainId,
			from:   validatorAlice,
			to:     validatorBob,
			amount: 1,
		},
		state: State{
			consumerChainId: ChainState{
				// Tx should not go through, ICS channel is not setup until first VSC packet has been relayed to consumer
				ValBalances: &map[string]uint{
					validatorAlice: 10000000000,
					validatorBob:   10000000000,
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
				ValPowers: &map[string]uint{
					validatorAlice: 511,
					validatorBob:   500,
					validatorCarol: 500,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  consumerChainId,
			from:   validatorAlice,
			to:     validatorBob,
			amount: 1,
		},
		state: State{
			consumerChainId: ChainState{
				// Now tx should execute
				ValBalances: &map[string]uint{
					validatorAlice: 9999999999,
					validatorBob:   10000000001,
				},
			},
		},
	},
	{
		action: UnbondTokensAction{
			chain:      providerChainId,
			unbondFrom: validatorAlice,
			sender:     validatorAlice,
			amount:     11000000,
		},
		state: State{
			providerChainId: ChainState{
				ValPowers: &map[string]uint{
					validatorAlice: 500,
					validatorBob:   500,
					validatorCarol: 500,
				},
			},
			consumerChainId: ChainState{
				ValPowers: &map[string]uint{
					// Voting power on consumer should not be affected yet
					validatorAlice: 511,
					validatorBob:   500,
					validatorCarol: 500,
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
				ValPowers: &map[string]uint{
					validatorAlice: 500,
					validatorBob:   500,
					validatorCarol: 500,
				},
			},
		},
	},
	// TODO: Test full unbonding functionality, considering liquidity after unbonding period, etc.
}
