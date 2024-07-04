package main

// stepsDelegate tests basic delegation and resulting validator power changes
func stepsDelegate(consumerName string) []Step {
	return []Step{
		{
			Action: DelegateTokensAction{
				Chain:  ChainID("provi"),
				From:   ValidatorID("alice"),
				To:     ValidatorID("alice"),
				Amount: 11000000,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
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
		{
			Action: SendTokensAction{
				Chain:  ChainID(consumerName),
				From:   ValidatorID("alice"),
				To:     ValidatorID("bob"),
				Amount: 1,
			},
			State: State{
				ChainID(consumerName): ChainState{
					// Tx should not go through, ICS channel is not setup until first VSC packet has been relayed to consumer
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 10000000000,
						ValidatorID("bob"):   10000000000,
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
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: SendTokensAction{
				Chain:  ChainID(consumerName),
				From:   ValidatorID("alice"),
				To:     ValidatorID("bob"),
				Amount: 1,
			},
			State: State{
				ChainID(consumerName): ChainState{
					// Now tx should execute
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9999999999,
						ValidatorID("bob"):   10000000001,
					},
				},
			},
		},
	}
}

// stepsUnbond tests unbonding and resulting validator power changes.
func stepsUnbond(consumerName string) []Step {
	return []Step{
		{
			Action: UnbondTokensAction{
				Chain:      ChainID("provi"),
				UnbondFrom: ValidatorID("alice"),
				Sender:     ValidatorID("alice"),
				Amount:     1000000,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// Voting power on consumer should not be affected yet
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
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
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
	}
}

// stepsCancelUnbond canceling unbonding operation for delegator and validator combination
// the steps perform a full unbonding where the unbonding delegation is removed from the unbonding queue
func stepsCancelUnbond(consumerName string) []Step {
	return []Step{
		{
			Action: UnbondTokensAction{
				Chain:      ChainID("provi"),
				UnbondFrom: ValidatorID("alice"),
				Sender:     ValidatorID("alice"),
				Amount:     1000000,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// Voting power on consumer should not be affected yet
						ValidatorID("alice"): 510,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
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
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: CancelUnbondTokensAction{
				Chain:     ChainID("provi"),
				Delegator: ValidatorID("alice"),
				Validator: ValidatorID("alice"),
				Amount:    1000000, // cancel unbonding the full amount
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510, // power restored
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// Voting power on consumer should not be affected yet
						ValidatorID("alice"): 509,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
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
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 510, // power restored on consumer
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
	}
}

// stepsRedelegate tests redelegation and resulting validator power changes.
func stepsRedelegate(consumerName string) []Step {
	return []Step{
		{
			Action: RedelegateTokensAction{
				Chain:    ChainID("provi"),
				Src:      ValidatorID("carol"),
				Dst:      ValidatorID("alice"),
				TxSender: ValidatorID("carol"),
				// redelegate s.t. alice has majority stake so non-faulty validators maintain more than
				// 2/3 voting power during downtime tests below, avoiding chain halt
				Amount: 400000000,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 910,
						ValidatorID("bob"):   500,
						// carol always uses a consumer assigned key
						ValidatorID("carol"): 100,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// Voting power changes not seen by consumer yet
						ValidatorID("alice"): 510,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
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
						// Now power changes are seen by consumer
						ValidatorID("alice"): 910,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 100,
					},
				},
			},
		},
	}
}
