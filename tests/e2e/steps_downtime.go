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
			action: downtimeSlashAction{
				chain:     chainID(consumerName),
				validator: validatorID("bob"),
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
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						// Downtime jailing and corresponding voting power change are processed by provider
						validatorID("bob"):   0,
						validatorID("carol"): 501,
					},
				},
<<<<<<< HEAD
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
=======
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						// Bob's stake may or may not be slashed at this point depending on comet vs cometmock
						// See https://github.com/cosmos/interchain-security/issues/1304
						ValidatorID("carol"): 501,
>>>>>>> 88499b7 (feat!: completed throttle v2 (provider changes + migration + testing) (#1321))
					},
				},
			},
		},
		// A block is incremented each action, hence why VSC is committed on provider,
		// and can now be relayed as packet to consumer
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						// VSC now seen on consumer
						validatorID("bob"):   0,
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
						// bob's stake should not be slashed
						// since the slash was initiated from consumer
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   0,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						// bob's stake should not be slashed
						// since the slash was initiated from consumer
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
		// Now we test provider initiated downtime/slashing
		{
			action: downtimeSlashAction{
				chain:     chainID("provi"),
				validator: validatorID("carol"),
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						// Non faulty validators still maintain just above 2/3 power here
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						// Carol's stake should be slashed and jailed
						// downtime slash was initiated from provider
						validatorID("carol"): 0,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
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
						validatorID("bob"):   500,
						validatorID("carol"): 495,
					},
				},
				chainID(consumerName): ChainState{
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
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID(consumerName): ChainState{
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

// stepsDowntimeWithOptOut returns steps validating that alice can incur downtime
// and not be slashed/jailed, since her voting power is less than 5% of the total.
//
// Note: 60 / (60 + 500 + 950) ~= 0.04
func stepsDowntimeWithOptOut(consumerName string) []Step {
	return []Step{
		{
			action: downtimeSlashAction{
				chain:     chainID(consumerName),
				validator: validatorID("alice"),
			},
			state: State{
				// powers not affected on either chain
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 60,
						validatorID("bob"):   500,
						validatorID("carol"): 950,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 60,
						validatorID("bob"):   500,
						validatorID("carol"): 950,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						// alice is not slashed or jailed due to soft opt out
						validatorID("alice"): 60,
						validatorID("bob"):   500,
						validatorID("carol"): 950,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 60,
						validatorID("bob"):   500,
						validatorID("carol"): 950,
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
			action: downtimeSlashAction{
				chain:     chainID(consumerName),
				validator: validatorID("bob"),
			},
<<<<<<< HEAD
			state: State{
				// slash packet queued on consumer, but powers not affected on either chain yet
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
=======
			State: State{
				// slash packet queued for bob on consumer, but powers not affected on either chain yet
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
>>>>>>> 88499b7 (feat!: completed throttle v2 (provider changes + migration + testing) (#1321))
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
					ConsumerPendingPacketQueueSize: uintPtr(1), // bob's downtime slash packet is queued
				},
			},
		},
		// Relay packets so bob is jailed on provider,
		// and consumer receives ack that provider recv the downtime slash.
		// The latter is necessary for the consumer to send the second downtime slash.
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   0, // bob is jailed
						validatorID("carol"): 500,
					},
<<<<<<< HEAD
					// no provider throttling engaged yet
					GlobalSlashQueueSize: uintPointer(0),
					ConsumerChainQueueSizes: &map[chainID]uint{
						chainID(consumerName): uint(0),
					},
=======
>>>>>>> 88499b7 (feat!: completed throttle v2 (provider changes + migration + testing) (#1321))
				},
				chainID(consumerName): ChainState{
					// VSC packet applying jailing is not yet relayed to consumer
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
					ConsumerPendingPacketQueueSize: uintPtr(0), // slash packet handled ack clears consumer queue
				},
			},
		},
		// Invoke carol downtime slash on consumer
		{
			action: downtimeSlashAction{
				chain:     chainID(consumerName),
				validator: validatorID("carol"),
			},
<<<<<<< HEAD
			state: State{
				// powers not affected on either chain yet
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   0,
						validatorID("carol"): 500,
					},
				},
				chainID(consumerName): ChainState{
					// VSC packet applying jailing is not yet relayed to consumer
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
=======
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500, // VSC packet jailing bob is not yet relayed to consumer
						ValidatorID("carol"): 500,
>>>>>>> 88499b7 (feat!: completed throttle v2 (provider changes + migration + testing) (#1321))
					},
					ConsumerPendingPacketQueueSize: uintPtr(1), // carol's downtime slash packet is queued
				},
			},
		},
		// Relay slash packet to provider, and ack back to consumer
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
<<<<<<< HEAD
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   0,
						validatorID("carol"): 500, // not slashed due to throttling
					},
					GlobalSlashQueueSize: uintPointer(1), // carol's slash request is throttled
					ConsumerChainQueueSizes: &map[chainID]uint{
						chainID(consumerName): uint(1),
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   0,
						validatorID("carol"): 500,
=======
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500, // slash packet for carol recv by provider, carol not slashed due to throttling
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0, // VSC packet applying bob jailing is also relayed and recv by consumer
						ValidatorID("carol"): 500,
>>>>>>> 88499b7 (feat!: completed throttle v2 (provider changes + migration + testing) (#1321))
					},
					ConsumerPendingPacketQueueSize: uintPtr(1), // slash packet bounced ack keeps carol's downtime slash packet queued
				},
			},
		},
		{
<<<<<<< HEAD
			action: slashThrottleDequeue{
				chain:            chainID(consumerName),
				currentQueueSize: 1,
				nextQueueSize:    0,
				// Slash meter replenish fraction is set to 10%, replenish period is 20 seconds, see config.go
				// Meter is initially at 10%, decremented to -23% from bob being jailed. It'll then take three replenishments
				// for meter to become positive again. 3*20 = 60 seconds + buffer = 80 seconds
				timeout: 80 * time.Second,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   0,
						validatorID("carol"): 0, // Carol is jailed upon packet being handled on provider
					},
					GlobalSlashQueueSize: uintPointer(0), // slash packets dequeued
					ConsumerChainQueueSizes: &map[chainID]uint{
						chainID(consumerName): 0,
=======
			Action: slashMeterReplenishmentAction{
				TargetValue: 0, // We just want slash meter to be non-negative

				// Slash meter replenish fraction is set to 10%, replenish period is 20 seconds, see config.go
				// Meter is initially at 10%, decremented to -23% from bob being jailed. It'll then take three replenishments
				// for meter to become positive again. 3*20 = 60 seconds + buffer = 100 seconds
				Timeout: 100 * time.Second,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500, // Carol still not slashed, packet must be retried
>>>>>>> 88499b7 (feat!: completed throttle v2 (provider changes + migration + testing) (#1321))
					},
				},
				chainID(consumerName): ChainState{
					// no updates received on consumer
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   0,
						validatorID("carol"): 500,
					},
					ConsumerPendingPacketQueueSize: uintPtr(1), // packet still queued
				},
			},
		},
		// Wait for retry delay period to pass.
		// Retry delay period is set to 30 seconds, see config.go,
		// wait this amount of time to elapse the period.
		{
			Action: waitTimeAction{
				WaitTime: 30 * time.Second,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumerName): ChainState{
					ConsumerPendingPacketQueueSize: uintPtr(1), // packet still queued
				},
			},
		},
		// Relay now that retry delay period has passed, confirm provider applies jailing
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
<<<<<<< HEAD
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   0,
						validatorID("carol"): 0,
					},
					GlobalSlashQueueSize: uintPointer(0),
					ConsumerChainQueueSizes: &map[chainID]uint{
						chainID(consumerName): 0,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						// throttled update gets to consumer
						validatorID("bob"):   0,
						validatorID("carol"): 0,
					},
=======
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 0, // jailed!
					},
				},
				ChainID(consumerName): ChainState{
					ConsumerPendingPacketQueueSize: uintPtr(0), // relayed slash packet handled ack clears consumer queue
>>>>>>> 88499b7 (feat!: completed throttle v2 (provider changes + migration + testing) (#1321))
				},
			},
		},
	}
}
