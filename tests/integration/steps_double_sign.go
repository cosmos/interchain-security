package main

// simulates double signing on provider and consumer chains
func stepsDoubleSign(consumerName, doubleSignChain, doubleSignValidator string) []Step {
	return []Step{
		// provider double sign
		{
			action: doublesignSlashAction{
				chain:     chainID("provi"),
				validator: validatorID("carol"),
			},
			state: State{
				// slash on provider
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				// not slashed on consumer yet
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		},
		{
			// power changed on provided, not on consumer
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500,
						validatorID("bob"):   500,
						validatorID("carol"): 0,
					},
				},
			},
		},
	}
}
