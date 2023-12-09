package main

// stepsDowntime tests validator jailing and slashing.
// No slashing should occur for downtime slash initiated from the consumer chain
// validators will simply be jailed in those cases
// If an infraction is committed on the provider chain then the validator will be slashed
func stepsMultiConsumerDowntimeFromConsumer(consumer1, consumer2 string) []Step {
	return []Step{
		{
			Action: DowntimeSlashAction{
				Chain:     ChainID(consumer1),
				Validator: ValidatorID("bob"),
			},
			State: State{
				// validator should be slashed on consumer, powers not affected on either chain yet
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
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			// Downtime jailing and corresponding voting power change are processed by provider
			// Validator powers are unchanged on consumer chains
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer1),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0,
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
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			// A block is incremented each action, hence why VSC is committed on provider,
			// and can now be relayed as packet to consumer
			// consumer1 will now see the validator power changes - consumer2 will not (had not been relayed)
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer1),
				Port:    "provider",
				Channel: 0, // consumer1 chan
			},
			State: State{
				// change propagated to consumer1
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						// VSC now seen on consumer1
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						// VSC has not arrived to on consumer2
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			// both consumer1 and consumer will now see the validator power changes
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer2),
				Port:    "provider",
				Channel: 1, // consumer2 chan
			},
			State: State{
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0, // both consumers see the change
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0, // both consumers see the change
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			Action: UnjailValidatorAction{
				Provider:  ChainID("provi"),
				Validator: ValidatorID("bob"),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						// bob's stake should not be slashed since slash comes from consumer1
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
				// change is not visible on consumer1
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 501,
					},
				},
				// change is not visible on consumer2
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			// relay to consumer 1
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer1),
				Port:    "provider",
				Channel: 0,
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
						ValidatorID("bob"):   500, // change has arrived to consumer1 (no slashing)
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0, // change has not arrived to consumer2
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			// relay to consumer2
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer2),
				Port:    "provider",
				Channel: 1, // consumer2 chan
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
						ValidatorID("bob"):   500, // change has arrived to consumer1 (no slashing)
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500, // change has arrived to consumer2 (no slashing)
						ValidatorID("carol"): 501,
					},
				},
			},
		},
	}
}

// stepsMultiConsumerDowntimeFromProvider tests validator jailing and slashing.
// When the infraction is committed on the provider chain then the validator will be slashed
func stepsMultiConsumerDowntimeFromProvider(consumer1, consumer2 string) []Step {
	return []Step{
		// Now we test provider initiated downtime/slashing
		{
			Action: DowntimeSlashAction{
				Chain:     ChainID("provi"),
				Validator: ValidatorID("carol"),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
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
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer1),
				Port:    "provider",
				Channel: 0, // consumer 1 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				// powers now changed
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				// not relayed yet - powers unchanged
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumer2),
				Port:    "provider",
				Channel: 1, // consumer2 channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
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
				// powers now changed
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
			Action: UnjailValidatorAction{
				Provider:  ChainID("provi"),
				Validator: ValidatorID("carol"),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495, // slashed because infraction was committed on provider
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
			Action: RelayPacketsAction{
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
						ValidatorID("carol"): 495,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495,
					},
				},
				// not relayed yet
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
			Action: RelayPacketsAction{
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
						ValidatorID("carol"): 495,
					},
				},
				ChainID(consumer1): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495,
					},
				},
				ChainID(consumer2): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495,
					},
				},
			},
		},
	}
}
