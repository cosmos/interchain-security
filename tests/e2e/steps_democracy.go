package main

func stepsDemocracy(consumerName string) []Step {
	return []Step{
		{
			Action: registerRepresentativeAction{
				chain:           chainID(consumerName),
				representatives: []validatorID{validatorID("alice"), validatorID("bob")},
				stakes:          []uint{100000000, 40000000},
			},
			State: State{
				chainID(consumerName): ChainState{
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
			Action: delegateTokensAction{
				chain:  chainID(consumerName),
				from:   validatorID("carol"),
				to:     validatorID("alice"),
				amount: 500000,
			},
			State: State{
				chainID(consumerName): ChainState{
					// Check that delegators on gov-consumer chain can change representative powers
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
					// Check that tokens are minted and distributed to representatives and their delegators
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
			Action: submitParamChangeProposalAction{
				chain:    chainID(consumerName),
				from:     validatorID("alice"),
				deposit:  10000001,
				subspace: "staking",
				key:      "MaxValidators",
				value:    105,
			},
			State: State{
				chainID(consumerName): ChainState{
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
			// Have accounts vote on something on the gov-consumer chain
			Action: voteGovProposalAction{
				chain:      chainID(consumerName),
				from:       []validatorID{validatorID("alice"), validatorID("bob")},
				vote:       []string{"yes", "no"},
				propNumber: 1,
			},
			State: State{
				chainID(consumerName): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9899999999,
						validatorID("bob"):   9960000001,
					},
					// Check that the parameter is changed on gov-consumer chain
					Params: &([]Param{{Subspace: "staking", Key: "MaxValidators", Value: "105"}}),
				},
			},
		},
		{
			Action: relayRewardPacketsToProviderAction{
				consumerChain: chainID(consumerName),
				providerChain: chainID("provi"),
				port:          "transfer",
				channel:       1,
			},
			State: State{
				chainID("provi"): ChainState{
					// Check that tokens are minted and sent to provider chain and distributed to validators and their delegators on provider chain
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
			Action: downtimeSlashAction{
				chain:     chainID(consumerName),
				validator: validatorID("bob"),
			},
			State: State{
				// validator should be slashed on consumer, powers not affected on either chain yet
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
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
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						// Downtime jailing and corresponding voting power change are processed by provider
						validatorID("bob"):   0,
						validatorID("carol"): 500,
					},
				},
				chainID(consumerName): ChainState{
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
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			State: State{
				chainID(consumerName): ChainState{
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
			Action: unjailValidatorAction{
				provider:  chainID("provi"),
				validator: validatorID("bob"),
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   0,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			State: State{
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
					// Check that slashing on the gov-consumer chain does not result in slashing for the representatives or their delegators
					RepresentativePowers: &map[validatorID]uint{
						validatorID("alice"): 100500000,
						validatorID("bob"):   40000000,
					},
				},
			},
		},
	}
}
