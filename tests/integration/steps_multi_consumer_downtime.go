package main

// stepsDowntime tests validator jailing and slashing.
func stepsMultiConsumerDowntimeFromConsumer(consumer1, consumer2 string) []Step {
	return []Step{
		{
			action: downtimeSlashAction{
				chain:      chainID(consumer1),
				validators: []validatorID{validatorID("bob")},
			},
			state: State{
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
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			state: State{
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
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer1 chan
			},
			state: State{
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
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 chan
			},
			state: State{
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
			action: unjailValidatorAction{
				provider:  chainID("provi"),
				validator: validatorID("bob"),
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						// 1% of bob's stake should be slashed as set in config.go
						validatorID("bob"):   495,
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
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 501,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495, // bob was slashed and changes relayed to consumer1
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
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 chan
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 501,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495, // bob was slashed and changes relayed to consumer1
						validatorID("carol"): 501,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495, // change has arrived to consumer2
						validatorID("carol"): 501,
					},
				},
			},
		},
	}
}

// stepsMultiConsumerDowntimeFromProvider tests validator jailing and slashing.
func stepsMultiConsumerDowntimeFromProvider(consumer1, consumer2 string) []Step {
	return []Step{
		// Now we test provider initiated downtime/slashing
		{
			action: downtimeSlashAction{
				chain:      chainID("provi"),
				validators: []validatorID{validatorID("carol")},
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 501,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumer 1 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0,
					},
				},
				// powers now changed
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 0,
					},
				},
				// not relayed yet - powers unchanged
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 1, // consumer2 channel
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
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
				// powers now changed
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
			action: unjailValidatorAction{
				provider:  chainID("provi"),
				validator: validatorID("carol"),
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 495,
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
						validatorID("carol"): 495,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 495,
					},
				},
				// not relayed yet
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
						validatorID("carol"): 495,
					},
				},
				chainID(consumer1): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 495,
					},
				},
				chainID(consumer2): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   495,
						validatorID("carol"): 495,
					},
				},
			},
		},
	}
}
