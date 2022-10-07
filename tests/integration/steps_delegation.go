package main

// stepsDelegate tests basic delegation and resulting validator power changes.
func stepsDelegate(consumerName string) []Step {
	return []Step{
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
				chainID(consumerName): ChainState{
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
				chain:  chainID(consumerName),
				from:   validatorID("alice"),
				to:     validatorID("bob"),
				amount: 1,
			},
			state: State{
				chainID(consumerName): ChainState{
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
			action: SendTokensAction{
				chain:  chainID(consumerName),
				from:   validatorID("alice"),
				to:     validatorID("bob"),
				amount: 1,
			},
			state: State{
				chainID(consumerName): ChainState{
					// Now tx should execute
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9999999999,
						validatorID("bob"):   10000000001,
					},
				},
			},
		},
	}
}

// stepsDelegate tests validatod unbonding, redelegation and resulting validator power changes.
func stepsUnbondRedelegate(consumerName string) []Step {
	return []Step{
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
				chainID(consumerName): ChainState{
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
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						// Now power changes are seen by consumer
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
	}
}
