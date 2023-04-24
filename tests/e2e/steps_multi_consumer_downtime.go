package main

// stepsDowntime tests validator jailing and slashing.
// No slashing should occur for downtime slash initiated from the consumer chain
// validators will simply be jailed in those cases
// If an infraction is committed on the provider chain then the validator will be slashed
func stepsMultiConsumerDowntimeFromConsumer(consumer1, consumer2 string) []Step {
	return []Step{
		{
			Action: downtimeSlashAction{
				chain:     chainID(consumer1),
				validator: validatorID("bob"),
			},
			State: State{
				// validator should be slashed on consumer, powers not affected on either chain yet
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
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			// Downtime jailing and corresponding voting power change are processed by provider
			// Validator powers are unchanged on consumer chains
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0,
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
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			// A block is incremented each action, hence why VSC is committed on provider,
			// and can now be relayed as packet to consumer
			// consumer1 will now see the validator power changes - consumer2 will not (had not been relayed)
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer1 chan
			},
			State: State{
				// change propagated to consumer1
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						// VSC now seen on consumer1
						validatorID("bob"):   0,
						validatorID("carol"): 501,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						// VSC has not arrived to on consumer2
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			// both consumer1 and consumer will now see the validator power changes
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 chan
			},
			State: State{
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0, // both consumers see the change
						validatorID("carol"): 501,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0, // both consumers see the change
						validatorID("carol"): 501,
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
						validatorID("alice"): 509,
						// bob's stake should not be slashed since slash comes from consumer1
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
				// change is not visible on consumer1
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0,
						validatorID("carol"): 501,
					},
				},
				// change is not visible on consumer2
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			// relay to consumer 1
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
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
						validatorID("bob"):   500, // change has arrived to consumer1 (no slashing)
						validatorID("carol"): 501,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0, // change has not arrived to consumer2
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			// relay to consumer2
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 chan
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
						validatorID("bob"):   500, // change has arrived to consumer1 (no slashing)
						validatorID("carol"): 501,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // change has arrived to consumer2 (no slashing)
						validatorID("carol"): 501,
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
			Action: downtimeSlashAction{
				chain:     chainID("provi"),
				validator: validatorID("carol"),
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
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
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer 1 channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				// powers now changed
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				// not relayed yet - powers unchanged
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
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
				// powers now changed
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
			Action: unjailValidatorAction{
				provider:  chainID("provi"),
				validator: validatorID("carol"),
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 495, // slashed because infraction was committed on provider
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
						validatorID("carol"): 495,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 495,
					},
				},
				// not relayed yet
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
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 495,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 495,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 495,
					},
				},
			},
		},
	}
}
