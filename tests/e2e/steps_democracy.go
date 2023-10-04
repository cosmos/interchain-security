package main

const consumerRewardDenom = "ibc/3C3D7B3BE4ECC85A0E5B52A3AEC3B7DFC2AA9CA47C37821E57020D6807043BE9"

func stepsDemocracy(consumerName string) []Step {
	return []Step{
		{
			Action: registerRepresentativeAction{
				Chain:           ChainID(consumerName),
				Representatives: []ValidatorID{ValidatorID("alice"), ValidatorID("bob")},
				Stakes:          []uint{100000000, 40000000},
			},
			State: State{
				ChainID(consumerName): ChainState{
					StakedTokens: &map[ValidatorID]uint{
						ValidatorID("alice"): 100000000,
						ValidatorID("bob"):   40000000,
					},
					Rewards: &Rewards{
						IsRewarded: map[ValidatorID]bool{
							ValidatorID("alice"): true,
							ValidatorID("bob"):   true,
							ValidatorID("carol"): false,
						},
						IsIncrementalReward: true,
						IsNativeDenom:       true,
					},
				},
			},
		},
		{
			Action: delegateTokensAction{
				Chain:  ChainID(consumerName),
				From:   ValidatorID("carol"),
				To:     ValidatorID("alice"),
				Amount: 500000,
			},
			State: State{
				ChainID(consumerName): ChainState{
					// Check that delegators on gov-consumer chain can change representative powers
					StakedTokens: &map[ValidatorID]uint{
						ValidatorID("alice"): 100500000,
						ValidatorID("bob"):   40000000,
					},
					// Check that delegating on gov-consumer does not change validator powers
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
					// Check that tokens are minted and distributed to representatives and their delegators
					Rewards: &Rewards{
						IsRewarded: map[ValidatorID]bool{
							ValidatorID("alice"): true,
							ValidatorID("bob"):   true,
							ValidatorID("carol"): true,
						},
						IsIncrementalReward: true,
						IsNativeDenom:       true,
					},
				},
			},
		},
		{
			// whitelisted legacy proposal can only handle ibctransfer.SendEnabled/ReceiveEnabled
			Action: submitParamChangeLegacyProposalAction{
				Chain:    ChainID(consumerName),
				From:     ValidatorID("alice"),
				Deposit:  10000001,
				Subspace: "transfer",
				Key:      "SendEnabled",
				Value:    true,
			},
			State: State{
				ChainID(consumerName): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9889999998,
						ValidatorID("bob"):   9960000001,
					},
					// Check that the "SendEnabled" transfer parameter is set to false
					Params: &([]Param{{Subspace: "transfer", Key: "SendEnabled", Value: "false"}}),
					Proposals: &map[uint]Proposal{
						1: ParamsProposal{
							Deposit:  10000001,
							Status:   "PROPOSAL_STATUS_VOTING_PERIOD",
							Subspace: "transfer",
							Key:      "SendEnabled",
							Value:    "true",
						},
					},
				},
			},
		},
		{
			// Have accounts vote on something on the gov-consumer chain
			Action: voteGovProposalAction{
				Chain:      ChainID(consumerName),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob")},
				Vote:       []string{"yes", "no"},
				PropNumber: 1,
			},
			State: State{
				ChainID(consumerName): ChainState{
					// Check that alice gets the prop deposit refunded
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9899999999,
						ValidatorID("bob"):   9960000001,
					},
					// Check that the prop passed
					Proposals: &map[uint]Proposal{
						1: ParamsProposal{
							Deposit:  10000001,
							Status:   "PROPOSAL_STATUS_PASSED",
							Subspace: "transfer",
							Key:      "SendEnabled",
							Value:    "true",
						},
					},
					// Check that the parameter is changed on gov-consumer chain
					Params: &([]Param{{Subspace: "transfer", Key: "SendEnabled", Value: "true"}}),
				},
			},
		},
		{
			Action: relayRewardPacketsToProviderAction{
				ConsumerChain: ChainID(consumerName),
				ProviderChain: ChainID("provi"),
				Port:          "transfer",
				Channel:       1,
			},
			State: State{
				ChainID("provi"): ChainState{
					// Check that tokens are not distributed before the denom has been registered
					Rewards: &Rewards{
						IsRewarded: map[ValidatorID]bool{
							ValidatorID("alice"): false,
							ValidatorID("bob"):   false,
							ValidatorID("carol"): false,
						},
						IsIncrementalReward: false,
						IsNativeDenom:       false,
					},
					// Check that the denom is not registered on provider chain
					RegisteredConsumerRewardDenoms: &[]string{},
				},
			},
		},
		{
			Action: submitChangeRewardDenomsProposalAction{
				Denom:   consumerRewardDenom,
				Deposit: 10000001,
				From:    ValidatorID("bob"),
			},
			State: State{
				ChainID("provi"): ChainState{
					// Denom not yet registered, gov prop needs to pass first
					RegisteredConsumerRewardDenoms: &[]string{},
				},
			},
		},
		{
			Action: voteGovProposalAction{
				Chain:      ChainID("provi"),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol")},
				Vote:       []string{"yes", "yes", "yes"},
				PropNumber: 2,
			},
			State: State{
				ChainID("provi"): ChainState{
					// Check that the denom is registered on provider chain
					RegisteredConsumerRewardDenoms: &[]string{consumerRewardDenom},
				},
			},
		},
		{
			Action: relayRewardPacketsToProviderAction{
				ConsumerChain: ChainID(consumerName),
				ProviderChain: ChainID("provi"),
				Port:          "transfer",
				Channel:       1,
			},
			State: State{
				ChainID("provi"): ChainState{
					// Check that tokens are minted and sent to provider chain and distributed to validators and their delegators on provider chain
					Rewards: &Rewards{
						IsRewarded: map[ValidatorID]bool{
							ValidatorID("alice"): true,
							ValidatorID("bob"):   true,
							ValidatorID("carol"): true,
						},
						IsIncrementalReward: false,
						IsNativeDenom:       false,
					},
				},
			},
		},
		{
			Action: downtimeSlashAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("bob"),
			},
			State: State{
				// validator should be slashed on consumer, powers not affected on either chain yet
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
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						// Downtime jailing and corresponding voting power change are processed by provider
						ValidatorID("bob"):   0,
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
		// A block is incremented each action, hence why VSC is committed on provider,
		// and can now be relayed as packet to consumer
		{
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						// VSC now seen on consumer
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
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
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
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
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
					// Check that slashing on the gov-consumer chain does not result in slashing for the representatives or their delegators
					StakedTokens: &map[ValidatorID]uint{
						ValidatorID("alice"): 100500000,
						ValidatorID("bob"):   40000000,
					},
				},
			},
		},
	}
}
