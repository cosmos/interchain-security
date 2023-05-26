package main

// simulates double signing on provider and vsc propagation to consumer chains
//
// Note: These steps would be affected by slash packet throttling, since the
// consumer-initiated slash steps are executed after consumer-initiated downtime
// slashes have already occurred. However slash packet throttling is
// psuedo-disabled in this test by setting the slash meter replenish
// fraction to 1.0 in the config file.
//
// only double sign on provider chain will cause slashing and tombstoning
func stepsMultiConsumerDoubleSign(consumer1, consumer2 string) []Step {
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
						validatorID("bob"):   500,
						validatorID("carol"): 0, // from 500 to 0
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 495, // not tombstoned on consumer1 yet
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 495, // not tombstoned on consumer2 yet
					},
				},
			},
		},
		{
			// relay power change to consumer1
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumer1),
				port:    "provider",
				channel: 0, // consumer1 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0, // tombstoning visible on consumer1
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 495, // tombstoning NOT YET visible on consumer2
					},
				},
			},
		},
		{
			// relay power change to consumer2
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumer2),
				port:    "provider",
				channel: 1, // consumer2 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0, // tombstoned on consumer2
					},
				},
			},
		},
		{
			// consumer double sign
			// nothing should happen - double sign from consumer is dropped
			action: doublesignSlashAction{
				chain:     chainID("consu"),
				validator: validatorID("bob"),
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumer1),
				port:    "provider",
				channel: 0, // consumer1 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // not tombstoned
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // not tombstoned
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // not tombstoned
						validatorID("carol"): 0,
					},
				},
			},
		},
		{
			// consumer1 learns about the double sign
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumer1),
				port:    "provider",
				channel: 0, // consumer1 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // not tombstoned
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // not tombstoned
						validatorID("carol"): 0,
					},
				},
			},
		},
		{
			// consumer2 learns about the double sign
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumer2),
				port:    "provider",
				channel: 1, // consumer2 channel
			},
			state: State{
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
			},
		},
	}
}
