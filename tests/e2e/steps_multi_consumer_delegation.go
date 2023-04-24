package main

// stepsDelegate tests basic delegation and resulting validator power changes.
func stepsMultiConsumerDelegate(consumer1, consumer2 string) []Step {
	return []Step{
		{
			// changes not visible on any consumer
			Action: delegateTokensAction{
				chain:  chainID("provi"),
				from:   validatorID("alice"),
				to:     validatorID("alice"),
				amount: 11000000,
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511, // this changes from 500
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay changes to consumer1
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer1 channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511, // changed
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500, // unchanged
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay changes to consumer2
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511, // changed
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
	}
}

// stepsMultiConsumerUnbond tests unbonding and resulting validator power changes.
// order of operations: unbond on provider -> relay to each consumer
func stepsMultiConsumerUnbond(consumer1, consumer2 string) []Step {
	return []Step{
		{
			Action: unbondTokensAction{
				chain:      chainID("provi"),
				unbondFrom: validatorID("alice"),
				sender:     validatorID("alice"),
				amount:     1000000,
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510, // change from 511
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511, // no change
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511, // no change
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay to consumer1
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer1 channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510, // change from 511
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511, // no change
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay to consumer2
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510, // change from 511
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
	}
}

// stepsMultiConsumerRedelegate tests redelegation and resulting validator power changes.
// order of operations: redelegate on provider -> relay to each consumer
func stepsMultiConsumerRedelegate(consumer1, consumer2 string) []Step {
	return []Step{
		{
			Action: redelegateTokensAction{
				chain:    chainID("provi"),
				src:      validatorID("alice"),
				dst:      validatorID("carol"),
				txSender: validatorID("alice"),
				// Leave alice with majority stake so non-faulty validators maintain more than
				// 2/3 voting power during downtime tests below, avoiding chain halt
				amount: 1000000,
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510, // no change
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510, // no change
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},

		{
			// relay to consumer1
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer1 channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509, // change from 510
						validatorID("bob"):   500,
						validatorID("carol"): 501, // change from 500
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510, // no change
						validatorID("bob"):   500,
						validatorID("carol"): 500, // no change
					},
				},
			},
		},
		{
			// relay to consumer2
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer1 channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509, // change from 510
						validatorID("bob"):   500,
						validatorID("carol"): 501, // change from 500
					},
				},
			},
		},
	}
}
