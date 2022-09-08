package main

import (
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
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
		action: submitConsumerProposalAction{
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
		action: voteGovProposalAction{
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
		action: startConsumerChainAction{
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
		action: addIbcConnectionAction{
			chainA:  chainID("consu"),
			chainB:  chainID("provi"),
			clientA: 0,
			clientB: 0,
			order:   "ordered",
		},
		state: State{},
	},
	{
		action: addIbcChannelAction{
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
		action: relayPacketsAction{
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
		action: relayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 510,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
			},
		},
	},
	{
		action: redelegateTokensAction{
			chain:    chainID("provi"),
			src:      validatorID("alice"),
			dst:      validatorID("carol"),
			txSender: validatorID("alice"),
			// Leave alice with majority stake so non-faulty validators maintain more than
			// 2/3 voting power during downtime tests below, avoiding chain halt
			amount: 1000000,
		},
		state: State{
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   500,
					validatorID("carol"): 501,
				},
			},
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					// Voting power changes not seen by consumer yet
					validatorID("alice"): 510,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
			},
		},
	},
	{
		action: relayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					// Now power changes are seen by consumer
					validatorID("alice"): 509,
					validatorID("bob"):   500,
					validatorID("carol"): 501,
				},
			},
		},
	},
	{
		action: downtimeSlashAction{
			chain: chainID("consu"),
			// TODO: First validator cannot be brought down until this issue is resolved:
			// https://github.com/cosmos/interchain-security/issues/263
			validator: validatorID("bob"),
		},
		state: State{
			// validator should be slashed on consumer, powers not affected on either chain yet
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   500,
					validatorID("carol"): 501,
				},
			},
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   500,
					validatorID("carol"): 501,
				},
			},
		},
	},
	{
		action: relayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					// Downtime jailing and corresponding voting power change are processed by provider
					validatorID("bob"):   0,
					validatorID("carol"): 501,
				},
			},
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   500,
					validatorID("carol"): 501,
				},
			},
		},
	},
	// A block is incremented each action, hence why VSC is committed on provider,
	// and can now be relayed as packet to consumer
	{
		action: relayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					// VSC now seen on consumer
					validatorID("bob"):   0,
					validatorID("carol"): 501,
				},
			},
		},
	},
	{
		action: unjailValidatorAction{
			provider:  chainID("provi"),
			validator: validatorID("bob"),
		},
		state: State{
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					// 1% of bob's stake should be slashed as set in config.go
					validatorID("bob"):   495,
					validatorID("carol"): 501,
				},
			},
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   0,
					validatorID("carol"): 501,
				},
			},
		},
	},
	{
		action: relayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   495,
					validatorID("carol"): 501,
				},
			},
		},
	},
	// Now we test provider initiated downtime/slashing
	{
		action: downtimeSlashAction{
			chain:     chainID("provi"),
			validator: validatorID("carol"),
		},
		state: State{
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					// Non faulty validators still maintain just above 2/3 power here
					validatorID("alice"): 509,
					validatorID("bob"):   495,
					validatorID("carol"): 0,
				},
			},
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   495,
					validatorID("carol"): 501,
				},
			},
		},
	},
	{
		action: relayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   495,
					validatorID("carol"): 0,
				},
			},
		},
	},
	{
		action: unjailValidatorAction{
			provider:  chainID("provi"),
			validator: validatorID("carol"),
		},
		state: State{
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   495,
					validatorID("carol"): 495,
				},
			},
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   495,
					validatorID("carol"): 0,
				},
			},
		},
	},
	{
		action: relayPacketsAction{
			chain:   chainID("provi"),
			port:    "provider",
			channel: 0,
		},
		state: State{
			chainID("consu"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 509,
					validatorID("bob"):   495,
					validatorID("carol"): 495,
				},
			},
		},
	},

	// TODO: Test full unbonding functionality, tracked as: https://github.com/cosmos/interchain-security/issues/311

}
