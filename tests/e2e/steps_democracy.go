package main

import gov "github.com/cosmos/cosmos-sdk/x/gov/types/v1"

var consumerRewardDenoms = []string{
	"ibc/3C3D7B3BE4ECC85A0E5B52A3AEC3B7DFC2AA9CA47C37821E57020D6807043BE9", // transfer channel-1
	"ibc/D549749C93524DA1831A4B3C850DFC1BA9060261BEDFB224B3B0B4744CD77A70", // transfer channel-2
}

func stepsDemocracy(consumerName string, expectRegisteredRewardDistribution bool) []Step {
	return []Step{
		{
			Action: RegisterRepresentativeAction{
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
						Denom:               "stake",
					},
					// Check that delegating on gov-consumer does not change validator powers
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: DelegateTokensAction{
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
						Denom:               "stake",
					},
				},
			},
		},
		{
			// whitelisted legacy proposal can only handle ibctransfer.SendEnabled/ReceiveEnabled
			Action: SubmitEnableTransfersProposalAction{
				Chain:   ChainID(consumerName),
				From:    ValidatorID("alice"),
				Deposit: 10000001,
				Title:   "Enable IBC Send",
			},
			State: State{
				ChainID(consumerName): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9889999998,
						ValidatorID("bob"):   9960000001,
					},
					// confirm the
					Proposals: &map[uint]Proposal{
						1: IBCTransferParamsProposal{
							Deposit: 10000001,
							Status:  gov.ProposalStatus_PROPOSAL_STATUS_VOTING_PERIOD.String(),
							Title:   "Enable IBC Send",
							Params:  IBCTransferParams{SendEnabled: true, ReceiveEnabled: true},
						},
					},
				},
			},
		},
		{
			// Have accounts vote on something on the gov-consumer chain
			Action: VoteGovProposalAction{
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
						1: IBCTransferParamsProposal{
							Deposit: 10000001,
							Status:  gov.ProposalStatus_PROPOSAL_STATUS_PASSED.String(),
							Title:   "Enable IBC Send",
							Params:  IBCTransferParams{SendEnabled: true, ReceiveEnabled: true},
						},
					},
				},
			},
		},
		{
			Action: RelayRewardPacketsToProviderAction{
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
						Denom:               consumerRewardDenoms[0],
					},
					// Check that the denom is not registered on provider chain
					RegisteredConsumerRewardDenoms: &[]string{},
				},
			},
		},
		{
			Action: SubmitChangeRewardDenomsProposalAction{
				Chain:   ChainID("provi"),
				Denoms:  consumerRewardDenoms,
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
			Action: VoteGovProposalAction{
				Chain:      ChainID("provi"),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol")},
				Vote:       []string{"yes", "yes", "yes"},
				PropNumber: 2,
			},
			State: State{
				ChainID("provi"): ChainState{
					// Check that the denom is registered on provider chain
					RegisteredConsumerRewardDenoms: &consumerRewardDenoms,
				},
			},
		},
		// Relay pending consumer rewards sent via the transfer channel-1
		{
			Action: RelayRewardPacketsToProviderAction{
				ConsumerChain: ChainID(consumerName),
				ProviderChain: ChainID("provi"),
				Port:          "transfer",
				Channel:       1,
			},
			State: State{
				ChainID("provi"): ChainState{
					Rewards: &Rewards{
						// expectRegisteredRewardDistribution == true
						// expect rewards to be distributed since IBC denoms are registered
						// and transfer channel-1 is associated to the consumer id
						IsRewarded: map[ValidatorID]bool{
							ValidatorID("alice"): expectRegisteredRewardDistribution,
							ValidatorID("bob"):   expectRegisteredRewardDistribution,
							ValidatorID("carol"): expectRegisteredRewardDistribution,
						},
						IsIncrementalReward: false,
						Denom:               consumerRewardDenoms[0],
					},
				},
			},
		},
		// Create a second consumer client on the provider
		{
			Action: CreateIbcClientAction{
				ChainA: ChainID("provi"),
				ChainB: ChainID(consumerName),
			},
			State: State{},
		},
		// Create a new IBC connection between the 2nd consumer client
		// and the existing provider client on the consumer
		{
			Action: AddIbcConnectionAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				ClientA: 1,
				ClientB: 0, // already created during the CCV handshake
			},
			State: State{},
		},
		// Create IBC transfer channel-2
		{
			Action: AddIbcChannelAction{
				ChainA:      ChainID("provi"),
				ChainB:      ChainID(consumerName),
				ConnectionA: 1,
				PortA:       "transfer",
				PortB:       "transfer",
				Order:       "unordered",
				Version:     "ics20-1",
			},
			State: State{},
		},
		// Transfer tokens from the consumer to the consumer reward pool
		// of the provider via the transfer channel-2
		{
			Action: TransferIbcTokenAction{
				Chain:   ChainID(consumerName),
				From:    ValidatorID("carol"),
				DstAddr: "cosmos1ap0mh6xzfn8943urr84q6ae7zfnar48am2erhd", // consumer reward pool address
				Amount:  1000000,
				Channel: 2,
				Memo:    "consumer chain rewards distribution", // no consumer Id in memo
			},
			State: State{},
		},
		// Relay the transfer packets from channel-2
		// and check that tokens are not distributed
		// since the packet isn't associated to a consumer id
		{
			Action: RelayRewardPacketsToProviderAction{
				ConsumerChain: ChainID(consumerName),
				ProviderChain: ChainID("provi"),
				Port:          "transfer",
				Channel:       2,
			},
			State: State{
				ChainID("provi"): ChainState{
					Rewards: &Rewards{
						IsRewarded: map[ValidatorID]bool{
							ValidatorID("alice"): false,
							ValidatorID("bob"):   false,
							ValidatorID("carol"): false,
						},
						IsIncrementalReward: false,
						Denom:               consumerRewardDenoms[1],
					},
				},
			},
		},
		// Transfer tokens from the consumer to the consumer reward pool
		// of the provider via the transfer channel-2 using the correct memo
		// to identify the consumer.
		// Note that in this case, the consumer reward denoms aren't filtered by the `provider_reward_denoms`
		// consumer parameter since the rewards are sent without going through the consumer distribution logic.
		{
			Action: TransferIbcTokenAction{
				Chain:   ChainID(consumerName),
				From:    ValidatorID("carol"),
				DstAddr: "cosmos1ap0mh6xzfn8943urr84q6ae7zfnar48am2erhd", // consumer reward pool address
				Amount:  1000000,
				Channel: 2,
				Memo:    `{"provider":{"consumerId":"0","chainId":"democ","memo":"ICS rewards"}}`,
			},
			State: State{},
		},
		// Relay the transfer packets from channel-2
		// and check that tokens are distributed
		{
			Action: RelayRewardPacketsToProviderAction{
				ConsumerChain: ChainID(consumerName),
				ProviderChain: ChainID("provi"),
				Port:          "transfer",
				Channel:       2,
			},
			State: State{
				ChainID("provi"): ChainState{
					Rewards: &Rewards{
						IsRewarded: map[ValidatorID]bool{
							// rewards should be distributed regardless
							// of the `provider_reward_denoms` consumer parameter
							ValidatorID("alice"): true,
							ValidatorID("bob"):   true,
							ValidatorID("carol"): true,
						},
						IsIncrementalReward: false,
						Denom:               consumerRewardDenoms[1],
					},
				},
			},
		},
		{
			Action: DowntimeSlashAction{
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
						// VSC now seen on consumer
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 500,
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
