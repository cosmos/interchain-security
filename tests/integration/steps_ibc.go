package main

func stepsIBCSend() []Step {
	return []Step{
		{
			action: sendIBCTokensAction{
				src:    "sover",
				dst:    "provi",
				from:   validatorID("bob"),
				to:     validatorID("bob"),
				amount: 12345,
			},
			state: State{},
		},
		{
			action: relayPacketsAction{
				chain:   chainID("sover"),
				port:    "transfer",
				channel: 0,
			},
			state: State{
				chainID("sover"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("bob"): 9500000000 - 12345,
					},
				},
			},
		},
	}
}
