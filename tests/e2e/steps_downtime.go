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
			Action: DowntimeSlashAction{
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
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
						// Bob's stake may or may not be slashed at this point depending on comet vs cometmock
						// See https://github.com/cosmos/interchain-security/issues/1304
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		// A block is incremented each action, hence why VSC is committed on provider,
		// and can now be relayed as packet to consumer
		{
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
			Action: UnjailValidatorAction{
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
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
			Action: UnjailValidatorAction{
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
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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

// stepsDowstepsDoubleDowntime time tests that a validator can get jailed twice
// on a consumer.
// These are the steps:
// - a validator is down on a consumer
// - the validator gets jailed on the provider (when the SlashPacket is received)
// - the validator gets removed from the consumer (when the VSCPacket is received)
// - the validator gets unjailed on the provider
// - the validator is added to the consumer (when the VSCPacket is received)
// - the validator is down again on the consumer
// - the validator gets jailed on the provider (when the SlashPacket is received)
// - the validator gets removed from the consumer (when the VSCPacket is received)
func stepsDoubleDowntime(consumerName string) []Step {
	return []Step{
		{
			Action: DowntimeSlashAction{
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
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
						// Bob's stake may or may not be slashed at this point depending on comet vs cometmock
						// See https://github.com/cosmos/interchain-security/issues/1304
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		// A block is incremented each action, hence why VSC is committed on provider,
		// and can now be relayed as packet to consumer
		{
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
			Action: UnjailValidatorAction{
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
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
		// Try to jail bob again on the consumer
		{
			Action: DowntimeSlashAction{
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
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
						// Bob's stake may or may not be slashed at this point depending on comet vs cometmock
						// See https://github.com/cosmos/interchain-security/issues/1304
						ValidatorID("carol"): 501,
					},
				},
			},
		},
		// A block is incremented each action, hence why VSC is committed on provider,
		// and can now be relayed as packet to consumer
		{
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
	}
}

// stepsDowntimeWithOptOut returns steps validating that alice can incur downtime
// and not be slashed/jailed, since her voting power is less than 5% of the total.
//
// Note: 60 / (60 + 500 + 950) ~= 0.04
func stepsDowntimeWithOptOut(consumerName string) []Step {
	return []Step{
		{
			Action: DowntimeSlashAction{
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
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
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
			Action: DowntimeSlashAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("bob"),
			},
			State: State{
				// slash packet queued for bob on consumer, but powers not affected on either chain yet
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
					ConsumerPendingPacketQueueSize: uintPtr(1), // bob's downtime slash packet is queued
				},
			},
		},
		// Relay packets so bob is jailed on provider,
		// and consumer receives ack that provider recv the downtime slash.
		// The latter is necessary for the consumer to send the second downtime slash.
		{
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0, // bob is jailed
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumerName): ChainState{
					// VSC packet applying jailing is not yet relayed to consumer
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
					ConsumerPendingPacketQueueSize: uintPtr(0), // slash packet handled ack clears consumer queue
				},
			},
		},
		// Invoke carol downtime slash on consumer
		{
			Action: DowntimeSlashAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("carol"),
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
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500, // VSC packet jailing bob is not yet relayed to consumer
						ValidatorID("carol"): 500,
					},
					ConsumerPendingPacketQueueSize: uintPtr(1), // carol's downtime slash packet is queued
				},
			},
		},
		// Relay slash packet to provider, and ack back to consumer
		{
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0,
			},
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
					},
					ConsumerPendingPacketQueueSize: uintPtr(1), // slash packet bounced ack keeps carol's downtime slash packet queued
				},
			},
		},
		{
			Action: SlashMeterReplenishmentAction{
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
					},
				},
				ChainID(consumerName): ChainState{
					// no updates received on consumer
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
					},
					ConsumerPendingPacketQueueSize: uintPtr(1), // packet still queued
				},
			},
		},
		// Wait for retry delay period to pass.
		// Retry delay period is set to 30 seconds, see config.go,
		// wait this amount of time to elapse the period.
		{
			Action: WaitTimeAction{
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
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0,
			},
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
				},
			},
		},
	}
}
