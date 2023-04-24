package main

import "time"

// stepsDowntime tests validator jailing and slashing.
//
// Note: These steps are not affected by slash packet throttling since
// only one consumer initiated slash is implemented. Throttling is also
// pseudo-disabled in this test by setting the slash meter replenish
// fraction to 1.0 in the config file.
//
// No slashing should occur for downtime slash initiated from the consumer chain
// validators will simply be jailed in those cases
// If an infraction is committed on the provider chain then the validator will be slashed
func stepsDowntime(consumerName string) []Step {
	return []Step{
		{
			Action: downtimeSlashAction{
				Chain:     ChainID(consumerName),
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
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						// Downtime jailing and corresponding voting power change are processed by provider
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		// A block is incremented each action, hence why VSC is committed on provider,
		// and can now be relayed as packet to consumer
		{
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						// VSC now seen on consumer
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			Action: unjailValidatorAction{
				Provider:  ChainID("provi"),
				Validator: ValidatorID("bob"),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						// bob's stake should not be slashed
						// since the slash was initiated from consumer
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						// bob's stake should not be slashed
						// since the slash was initiated from consumer
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		// Now we test provider initiated downtime/slashing
		{
			Action: downtimeSlashAction{
				Chain:     ChainID("provi"),
				Validator: ValidatorID("carol"),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						// Carol's stake should be slashed and jailed
						// downtime slash was initiated from provider
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		{
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
			},
		},
		{
			Action: unjailValidatorAction{
				Provider:  ChainID("provi"),
				Validator: ValidatorID("carol"),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495,
					},
				},
				ChainID(consumerName): ChainState{
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
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID(consumerName): ChainState{
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

// stepsDowntimeWithOptOut returns steps validating that alice can incur downtime
// and not be slashed/jailed, since her voting power is less than 5% of the total.
//
// Note: 60 / (60 + 500 + 950) ~= 0.04
func stepsDowntimeWithOptOut(consumerName string) []Step {
	return []Step{
		{
			Action: downtimeSlashAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("alice"),
			},
			State: State{
				// powers not affected on either chain
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 60,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 950,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 60,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 950,
					},
				},
			},
		},
		{
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// alice is not slashed or jailed due to soft opt out
						ValidatorID("alice"): 60,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 950,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 60,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 950,
					},
				},
			},
		},
	}
}

// stepsThrottledDowntime creates two consumer initiated downtime slash events and relays packets
// No slashing should occur since the downtime slash was initiated from the consumer chain
// Validators will simply be jailed
func stepsThrottledDowntime(consumerName string) []Step {
	return []Step{
		{
			Action: downtimeSlashAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("bob"),
			},
			State: State{
				// powers not affected on either chain yet
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: downtimeSlashAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("carol"),
			},
			State: State{
				// powers not affected on either chain yet
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500, // not slashed due to throttling
					},
					GlobalSlashQueueSize: uintPointer(1), // carol's slash request is throttled
					ConsumerChainQueueSizes: &map[ChainID]uint{
						ChainID(consumerName): uint(1),
					},
				},
				ChainID(consumerName): ChainState{
					// no updates received on consumer
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: slashThrottleDequeue{
				Chain:            ChainID(consumerName),
				CurrentQueueSize: 1,
				NextQueueSize:    0,
				// Slash meter replenish fraction is set to 10%, replenish period is 20 seconds, see config.go
				// Meter is initially at 10%, decremented to -23% from bob being jailed. It'll then take three replenishments
				// for meter to become positive again. 3*20 = 60 seconds + buffer = 80 seconds
				Timeout: 80 * time.Second,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 0, // Carol is jailed upon packet being handled on provider
					},
					GlobalSlashQueueSize: uintPointer(0), // slash packets dequeued
					ConsumerChainQueueSizes: &map[ChainID]uint{
						ChainID(consumerName): 0,
					},
				},
				ChainID(consumerName): ChainState{
					// no updates received on consumer
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		// A block is incremented each action, hence why VSC is committed on provider,
		// and can now be relayed as packet to consumer
		{
			Action: relayPacketsAction{
				Chain:   ChainID("provi"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 0,
					},
					GlobalSlashQueueSize: uintPointer(0),
					ConsumerChainQueueSizes: &map[ChainID]uint{
						ChainID(consumerName): 0,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						// throttled update gets to consumer
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 0,
					},
				},
			},
		},
	}
}
