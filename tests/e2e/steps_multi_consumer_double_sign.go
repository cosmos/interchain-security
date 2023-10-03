package main

// simulates double signing on provider and vsc propagation to consumer chains
//
// Note: These steps would be affected by slash packet throttling, since the
// consumer-initiated slash steps are executed after consumer-initiated downtime
// slashes have already occurred. However slash packet throttling is
// pseudo-disabled in this test by setting the slash meter replenish
// fraction to 1.0 in the config file.
//
// only double sign on provider chain will cause slashing and tombstoning
func stepsMultiConsumerDoubleSign(consumer1, consumer2 string) []Step {
	return []Step{
		{
			// provider double sign
			Action: doublesignSlashAction{
				Chain:     ChainID("provi"),
				Validator: ValidatorID("carol"),
			},
			State: State{
				// slash on provider
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0, // from 500 to 0
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495, // not tombstoned on consumer1 yet
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495, // not tombstoned on consumer2 yet
					},
				},
			},
		},
		{
			// relay power change to consumer1
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer1),
				Port:    "provider",
				Channel: 0, // consumer1 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0, // tombstoning visible on consumer1
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495, // tombstoning NOT YET visible on consumer2
					},
				},
			},
		},
		{
			// relay power change to consumer2
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer2),
				Port:    "provider",
				Channel: 1, // consumer2 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0, // tombstoned on consumer2
					},
				},
			},
		},
		{
			// consumer double sign
			// nothing should happen - double sign from consumer is dropped
			Action: doublesignSlashAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("bob"),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
			},
		},
		{
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer1),
				Port:    "provider",
				Channel: 0, // consumer1 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500, // not tombstoned
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500, // not tombstoned
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500, // not tombstoned
						ValidatorID("carol"): 0,
					},
				},
			},
		},
		{
			// consumer1 learns about the double sign
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer1),
				Port:    "provider",
				Channel: 0, // consumer1 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500, // not tombstoned
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500, // not tombstoned
						ValidatorID("carol"): 0,
					},
				},
			},
		},
		{
			// consumer2 learns about the double sign
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer2),
				Port:    "provider",
				Channel: 1, // consumer2 channel
			},
			State: State{
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
			},
		},
	}
}
