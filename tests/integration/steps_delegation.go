package main

// stepsDelegate tests basic delegation and resulting validator power changes.
func stepsDelegate(consumerNames []string) []Step {
	setInitialState := func(names []string) State {
		st := State{
			chainID("provi"): ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 511,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
			},
		}
		for _, consumerName := range consumerNames {
			st[chainID(consumerName)] = ChainState{
				ValPowers: &map[validatorID]uint{
					validatorID("alice"): 500,
					validatorID("bob"):   500,
					validatorID("carol"): 500,
				},
			}
		}
		return st
	}

	s := []Step{
		{
			action: delegateTokensAction{
				chain:  chainID("provi"),
				from:   validatorID("alice"),
				to:     validatorID("alice"),
				amount: 11000000,
			},
			state: setInitialState(consumerNames),
		},
	}

	for i, consumerName := range consumerNames {
		s = append(s, []Step{
			// {
			// 	action: SendTokensAction{
			// 		chain:  chainID(consumerName),
			// 		from:   validatorID("alice"),
			// 		to:     validatorID("bob"),
			// 		amount: 1,
			// 	},
			// 	state: State{
			// 		chainID(consumerName): ChainState{
			// 			// Tx should not go through, ICS channel is not setup until first VSC packet has been relayed to consumer
			// 			ValBalances: &map[validatorID]uint{
			// 				validatorID("alice"): 10000000000,
			// 				validatorID("bob"):   10000000000,
			// 			},
			// 		},
			// 	},
			// },
			{
				action: relayPacketsAction{
					chain:   chainID("provi"),
					port:    "provider",
					channel: uint(i),
				},
				state: State{
					chainID(consumerName): ChainState{
						ValPowers: &map[validatorID]uint{
							validatorID("alice"): 511,
							validatorID("bob"):   500,
							validatorID("carol"): 500,
						},
					},
				},
			},
			// {
			// 	action: SendTokensAction{
			// 		chain:  chainID(consumerName),
			// 		from:   validatorID("alice"),
			// 		to:     validatorID("bob"),
			// 		amount: 1,
			// 	},
			// 	state: State{
			// 		chainID(consumerName): ChainState{
			// 			// Now tx should execute
			// 			ValBalances: &map[validatorID]uint{
			// 				validatorID("alice"): 9999999999,
			// 				validatorID("bob"):   10000000001,
			// 			},
			// 		},
			// 	},
			// },
		}...)
	}
	return s
}

// stepsUnbond tests unbonding and resulting validator power changes.
// order of operations:
// - unbond on provider
//   - relay to each consumer
func stepsUnbond(consumerNames []string) []Step {
	s := []Step{}
	unbond := Step{
		action: unbondTokensAction{
			chain:      chainID("provi"),
			unbondFrom: validatorID("alice"),
			sender:     validatorID("alice"),
			amount:     1000000,
		},
	}
	// unbond change is immediately visible on provider
	unbondState := State{
		chainID("provi"): ChainState{
			ValPowers: &map[validatorID]uint{
				validatorID("alice"): 510,
				validatorID("bob"):   500,
				validatorID("carol"): 500,
			},
		},
	}

	for _, consumerName := range consumerNames {
		// unbond change is not yet visible on any of the consumers
		// relaying needs to happen first
		unbondState[chainID(consumerName)] = ChainState{
			ValPowers: &map[validatorID]uint{
				validatorID("alice"): 511,
				validatorID("bob"):   500,
				validatorID("carol"): 500,
			},
		}
	}
	unbond.state = unbondState

	s = append(s, unbond)

	// We must relay to all consumers so VSC can be applied
	for i, consumerName := range consumerNames {
		s = append(s, Step{
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: uint(i),
			},
			state: State{
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 510,
						validatorID("bob"):   500,
						validatorID("carol"): 500,
					},
				},
			},
		})
	}

	return s
}

// stepsDelegate tests redelegation and resulting validator power changes.
// order of operations:
// - redelegate on provider
//   - relay to each consumer
func stepsRedelegate(consumerNames []string) []Step {
	s := []Step{}

	redelegate := Step{
		action: redelegateTokensAction{
			chain:    chainID("provi"),
			src:      validatorID("alice"),
			dst:      validatorID("carol"),
			txSender: validatorID("alice"),
			// Leave alice with majority stake so non-faulty validators maintain more than
			// 2/3 voting power during downtime tests below, avoiding chain halt
			amount: 1000000,
		},
	}
	redelegateState := State{
		chainID("provi"): ChainState{
			ValPowers: &map[validatorID]uint{
				validatorID("alice"): 509,
				validatorID("bob"):   500,
				validatorID("carol"): 501,
			},
		},
	}

	for _, consumerName := range consumerNames {
		redelegateState[chainID(consumerName)] = ChainState{
			ValPowers: &map[validatorID]uint{
				// Powers unchanged on consumers
				validatorID("alice"): 510,
				validatorID("bob"):   500,
				validatorID("carol"): 500,
			},
		}
	}
	redelegate.state = redelegateState

	s = append(s, redelegate)

	for i, consumerName := range consumerNames {
		s = append(s, Step{
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: uint(i),
			},
			state: State{
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						// Now power changes are seen by consumer
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		})
	}

	return s
}
