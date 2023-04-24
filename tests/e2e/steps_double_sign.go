package main

// Steps that make carol double sign on the provider, and bob double sign on a single consumer
func stepsDoubleSignOnProviderAndConsumer(consumerName string) []Step {
	return []Step{
		{
			// provider double sign
			Action: doublesignSlashAction{
				chain:     chainID("provi"),
				validator: validatorID("carol"),
			},
			State: State{
				// slash on provider
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0, // from 500 to 0
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 495, // not tombstoned on consumerName yet
					},
				},
			},
		},
		{
			// relay power change to consumerName
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0, // consumerName channel
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0, // tombstoning visible on consumerName
					},
				},
			},
		},
		{
			// consumer double sign
			// provider will only log the double sign slash
			// stepsSubmitEquivocationProposal will cause the double sign slash to be executed
			Action: doublesignSlashAction{
				chain:     chainID("consu"),
				validator: validatorID("bob"),
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
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
			Action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			State: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // not tombstoned
						validatorID("carol"): 0,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // not tombstoned
						validatorID("carol"): 0,
					},
				},
			},
		},
		{
			// consumer learns about the double sign
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
						validatorID("carol"): 0,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500, // not tombstoned
						validatorID("carol"): 0,
					},
				},
			},
		},
	}
}
