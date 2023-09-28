package main

// Steps that make carol double sign on the provider, and bob double sign on a single consumer
func stepsDoubleSignOnProviderAndConsumer(consumerName string) []Step {
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
			Action: relayPacketsAction{
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
		{
			// consumer double sign
			// provider will only log the double sign slash
			// stepsSubmitEquivocationProposal will cause the double sign slash to be executed
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
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500, // not tombstoned
						ValidatorID("carol"): 0,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500, // not tombstoned
						ValidatorID("carol"): 0,
					},
				},
			},
		},
		{
			// consumer learns about the double sign
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0,
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
						ValidatorID("bob"):   500, // not tombstoned
						ValidatorID("carol"): 0,
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
			Action: doublesignSlashAction{
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
		// and jail bob on the provider
		{
			Action: startConsumerEvidenceDetectorAction{
				Chain: ChainID(consumerName),
			},
			State: State{
				ChainID(providerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
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
			Action: relayPacketsAction{
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
