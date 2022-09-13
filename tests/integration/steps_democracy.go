package main

import (
	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
)

var democracySteps = []Step{
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
			consumerChain: chainID("democ"),
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
						Chain:         chainID("democ"),
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
						Chain:         chainID("democ"),
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
			consumerChain:  chainID("democ"),
			providerChain:  chainID("provi"),
			genesisChanges: ".app_state.ccvconsumer.params.blocks_per_distribution_transmission = \"10\"",
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
			chainID("democ"): ChainState{
				ValBalances: &map[validatorID]uint{
					validatorID("alice"): 10000000000,
					validatorID("bob"):   10000000000,
				},
			},
		},
	},
	{
		action: SendTokensAction{
			chain:  chainID("democ"),
			from:   validatorID("alice"),
			to:     validatorID("bob"),
			amount: 1,
		},
		state: State{
			chainID("democ"): ChainState{
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
			chainA:  chainID("democ"),
			chainB:  chainID("provi"),
			clientA: 0,
			clientB: 0,
			order:   "ordered",
		},
		state: State{},
	},
	{
		action: addIbcChannelAction{
			chainA:      chainID("democ"),
			chainB:      chainID("provi"),
			connectionA: 0,
			portA:       "consumer",
			portB:       "provider",
			order:       "ordered",
		},
		state: State{},
	},
	{
		action: transferChannelCompleteAction{
			chainA:      chainID("democ"),
			chainB:      chainID("provi"),
			connectionA: 0,
			portA:       "transfer",
			portB:       "transfer",
			order:       "unordered",
			channelA:    1,
			channelB:    1,
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
			chainID("democ"): ChainState{
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
			chain:  chainID("democ"),
			from:   validatorID("alice"),
			to:     validatorID("bob"),
			amount: 1,
		},
		state: State{
			chainID("democ"): ChainState{
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
			chainID("democ"): ChainState{
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
			chain:  chainID("democ"),
			from:   validatorID("alice"),
			to:     validatorID("bob"),
			amount: 1,
		},
		state: State{
			chainID("democ"): ChainState{
				// Now tx should execute
				ValBalances: &map[validatorID]uint{
					validatorID("alice"): 9999999999,
					validatorID("bob"):   10000000001,
				},
			},
		},
	},
	// sanity checks end here
	{
		action: registerRepresentativeAction{
			chain:           chainID("democ"),
			representatives: []validatorID{validatorID("alice"), validatorID("bob")},
			stakes:          []uint{100000000, 40000000},
		},
		state: State{
			chainID("democ"): ChainState{
				RepresentativePowers: &map[validatorID]uint{
					validatorID("alice"): 100000000,
					validatorID("bob"):   40000000,
				},
				Rewards: &Rewards{
					IsRewarded: map[validatorID]bool{
						validatorID("alice"): true,
						validatorID("bob"):   true,
						validatorID("carol"): false,
					},
					IsIncrementalReward: true,
					IsNativeDenom:       true,
				},
			},
		},
	},
	{
		action: delegateTokensAction{
			chain:  chainID("democ"),
			from:   validatorID("carol"),
			to:     validatorID("alice"),
			amount: 500000,
		},
		state: State{
			chainID("democ"): ChainState{
				//Check that delegators on gov-consumer chain can change representative powers
				RepresentativePowers: &map[validatorID]uint{
					validatorID("alice"): 100500000,
					validatorID("bob"):   40000000,
				},
				// Check that delegating on gov-consumer does not change validator powers
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 511,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
				//Check that tokens are minted and distributed to representatives and their delegators
				Rewards: &Rewards{
					IsRewarded: map[validatorID]bool{
						validatorID("alice"): true,
						validatorID("bob"):   true,
						validatorID("carol"): true,
					},
					IsIncrementalReward: true,
					IsNativeDenom:       true,
				},
			},
		},
	},
	{
		action: submitParamChangeProposalAction{
			chain:    chainID("democ"),
			from:     validatorID("alice"),
			deposit:  10000001,
			subspace: "staking",
			key:      "MaxValidators",
			value:    105,
		},
		state: State{
			chainID("democ"): ChainState{
				ValBalances: &map[validatorID]uint{
					validatorID("alice"): 9889999998,
					validatorID("bob"):   9960000001,
				},
				Proposals: &map[uint]Proposal{
					1: ParamsProposal{
						Deposit:  10000001,
						Status:   "PROPOSAL_STATUS_VOTING_PERIOD",
						Subspace: "staking",
						Key:      "MaxValidators",
						Value:    "105",
					},
				},
			},
		},
	},
	{
		//Have accounts vote on something on the gov-consumer chain
		action: voteGovProposalAction{
			chain:      chainID("democ"),
			from:       []validatorID{validatorID("alice"), validatorID("bob")},
			vote:       []string{"yes", "no"},
			propNumber: 1,
		},
		state: State{
			chainID("democ"): ChainState{
				ValBalances: &map[validatorID]uint{
					validatorID("alice"): 9899999999,
					validatorID("bob"):   9960000001,
				},
				//Check that the parameter is changed on gov-consumer chain
				Params: &([]Param{{Subspace: "staking", Key: "MaxValidators", Value: "105"}}),
			},
		},
	},
	{
		action: relayRewardPacketsToProviderAction{
			consumerChain: chainID("democ"),
			providerChain: chainID("provi"),
			port:          "transfer",
			channel:       1,
		},
		state: State{
			chainID("provi"): ChainState{
				//Check that tokens are minted and sent to provider chain and distributed to validators and their delegators on provider chain
				Rewards: &Rewards{
					IsRewarded: map[validatorID]bool{
						validatorID("alice"): true,
						validatorID("bob"):   true,
						validatorID("carol"): true,
					},
					IsIncrementalReward: false,
					IsNativeDenom:       false,
				},
			},
		},
	},
	{
		action: downtimeSlashAction{
			chain: chainID("democ"),
			// TODO: First validator cannot be brought down until this issue is resolved:
			// https://github.com/cosmos/interchain-security/issues/263
			validator: validatorID("bob"),
		},
		state: State{
			// validator should be slashed on consumer, powers not affected on either chain yet
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 511,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
			},
			chainID("democ"): ChainState{
				ValPowers: &map[validatorID]uint{
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
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 511,
					// Downtime jailing and corresponding voting power change are processed by provider
					validatorID("bob"):   0,
					validatorID("carol"): 500,
				},
			},
			chainID("democ"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 511,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
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
			chainID("democ"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 511,
					// VSC now seen on consumer
					validatorID("bob"):   0,
					validatorID("carol"): 500,
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
					validatorID("alice"): 511,
					// 1% of bob's stake should be slashed as set in config.go
					validatorID("bob"):   495,
					validatorID("carol"): 500,
				},
			},
			chainID("democ"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 511,
					validatorID("bob"):   0,
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
			chainID("democ"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 511,
					validatorID("bob"):   495,
					validatorID("carol"): 500,
				},
				//Check that slashing on the gov-consumer chain does not result in slashing for the representatives or their delegators
				RepresentativePowers: &map[validatorID]uint{
					validatorID("alice"): 100500000,
					validatorID("bob"):   40000000,
				},
			},
		},
	},
}
