package main

// stepsDelegate tests basic delegation and resulting validator power changes.
func stepsMultiConsumerDelegate(consumer1, consumer2 string) []Step {
	return []Step{
		{
			// changes not visible on any consumer
			Action: delegateTokensAction{
				Chain:  ChainID("provi"),
				From:   ValidatorID("alice"),
				To:     ValidatorID("alice"),
				Amount: 11000000,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511, // this changes from 500
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay changes to consumer1
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0, // consumer1 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511, // changed
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500, // unchanged
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay changes to consumer2
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 1, // consumer2 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511, // changed
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
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
				Chain:      ChainID("provi"),
				UnbondFrom: ValidatorID("alice"),
				Sender:     ValidatorID("alice"),
				Amount:     1000000,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510, // change from 511
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511, // no change
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511, // no change
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay to consumer1
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0, // consumer1 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510, // change from 511
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511, // no change
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay to consumer2
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 1, // consumer2 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510, // change from 511
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
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
				Chain:    ChainID("provi"),
				Src:      ValidatorID("alice"),
				Dst:      ValidatorID("carol"),
				TxSender: ValidatorID("alice"),
				// Leave alice with majority stake so non-faulty validators maintain more than
				// 2/3 voting power during downtime tests below, avoiding chain halt
				Amount: 1000000,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510, // no change
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510, // no change
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},

		{
			// relay to consumer1
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0, // consumer1 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509, // change from 510
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501, // change from 500
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510, // no change
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500, // no change
					},
				},
			},
		},
		{
			// relay to consumer2
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 1, // consumer1 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509, // change from 510
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501, // change from 500
					},
				},
			},
		},
	}
}
