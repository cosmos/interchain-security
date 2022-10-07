package main

func stepsDemocracy(consumerName string) []Step {
	return []Step{
		{
			action: registerRepresentativeAction{
				chain:           chainID(consumerName),
				representatives: []validatorID{validatorID("alice"), validatorID("bob")},
				stakes:          []uint{100000000, 40000000},
			},
			state: State{
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
			action: delegateTokensAction{
				chain:  chainID(consumerName),
				from:   validatorID("carol"),
				to:     validatorID("alice"),
				amount: 500000,
			},
			state: State{
				chainID(consumerName): ChainState{
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
				chain:    chainID(consumerName),
				from:     validatorID("alice"),
				deposit:  10000001,
				subspace: "staking",
				key:      "MaxValidators",
				value:    105,
			},
			state: State{
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
			//Have accounts vote on something on the gov-consumer chain
			action: voteGovProposalAction{
				chain:      chainID(consumerName),
				from:       []validatorID{validatorID("alice"), validatorID("bob")},
				vote:       []string{"yes", "no"},
				propNumber: 1,
			},
			state: State{
				chainID(consumerName): ChainState{
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
				consumerChain: chainID(consumerName),
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
				chain: chainID(consumerName),
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
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			state: State{
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
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID(consumerName): ChainState{
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
}
