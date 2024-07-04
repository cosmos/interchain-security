package main

// Steps that make carol double sign on the provider, and this power change propagates to consumer chain `consumerName`
func stepsDoubleSignOnProvider(consumerName string) []Step {
	return []Step{
		{
			// provider double sign
			Action: DoublesignSlashAction{
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
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 495, // not tombstoned on consumerName yet
					},
				},
			},
		},
		{
			// relay power change to consumerName
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0, // consumerName channel
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 0, // tombstoning visible on consumerName
					},
				},
			},
		},
	}
}

// Steps that make bob double sign on the consumer
func stepsCauseDoubleSignOnConsumer(consumerName, providerName string) []Step {
	return []Step{
		{
			Action: DoublesignSlashAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("bob"),
			},
			State: State{
				ChainID(providerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
					StakedTokens: &map[ValidatorID]uint{
						ValidatorID("alice"): 500000000,
						ValidatorID("bob"):   500000000,
						ValidatorID("carol"): 500000000,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		// detect the double voting infraction
		// and jail and slashing of bob on the provider
		{
			Action: StartConsumerEvidenceDetectorAction{
				Chain: ChainID(consumerName),
			},
			State: State{
				ChainID(providerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
					},
					// "bob" gets slashed on the provider chain, hence representative
					// power is 500000000 - 0.05 * 500000000 = 475000000
					StakedTokens: &map[ValidatorID]uint{
						ValidatorID("alice"): 500000000,
						ValidatorID("bob"):   475000000,
						ValidatorID("carol"): 500000000,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		// consumer learns about the jailing
		{
			Action: RelayPacketsAction{
				ChainA:  ChainID(providerName),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID(providerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
					},
					StakedTokens: &map[ValidatorID]uint{
						ValidatorID("alice"): 500000000,
						ValidatorID("bob"):   475000000,
						ValidatorID("carol"): 500000000,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
	}
}
