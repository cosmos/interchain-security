package main

// simulates double signing on provider and vsc propagation to consumer chains
// steps continue from downtime tests state
func stepsDoubleSign(consumer1, consumer2 string) []Step {
	return []Step{
		{
			// provider double sign
			action: doublesignSlashAction{
				chain:     chainID("provi"),
				validator: validatorID("carol"),
			},
			state: State{
				// slash on provider
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0, // from 495 to 0
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 495, // not slashed on consumer1 yet
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 495, // not slashed on consumer2 yet
					},
				},
			},
		},
		{
			// relay power change to consumer1
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer1 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0, // slash visible on consumer1
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 495, // slash NOT YET visible on consumer2
					},
				},
			},
		},
		{
			// relay power change to consumer2
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0, // slash visible on consumer2
					},
				},
			},
		},
		{
			// consumer double sign
			// no changes are visible until relayed from consumer to provider
			action: doublesignSlashAction{
				chain:     chainID("consu"),
				validator: validatorID("bob"),
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0,
					},
				},
			},
		},
		{
			// provider learns about the infraction and slashes on provider chain
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer1 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0, // from 495 to 0
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495, // from 495 to 0
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495, // not slashed yet
						validatorID("carol"): 0,
					},
				},
			},
		},
		{
			// consumer1 learns about the slash and powerchanges
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer1 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0, // from 495 to 0
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495, // not slashed yet
						validatorID("carol"): 0,
					},
				},
			},
		},
		{
			// consumer1 learns about the slash and powerchanges
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 channel
			},
			state: State{
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0, // from 495 to 0
						validatorID("carol"): 0,
					},
				},
			},
		},
	}
}
