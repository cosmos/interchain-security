package main

import clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"

// this creates new clients on both chains and a connection (connection-0) between them
// connection-0 is used to create a transfer channel between the chains
// the transfer channel is maintained during the changeover process, meaning that
// the consumer chain will be able to send rewards to the provider chain using the old channel
// as opposed to creating a new transfer channel which happens for new consumers
func stepsSovereignTransferChan() []Step {
	return []Step{
		{
			Action: createIbcClientsAction{
				ChainA: ChainID("sover"),
				ChainB: ChainID("provi"),
			},
			State: State{},
		},
		{
			// this will create channel-0 connection end on both chain
			Action: addIbcChannelAction{
				ChainA:      ChainID("sover"),
				ChainB:      ChainID("provi"),
				ConnectionA: 0,
				PortA:       "transfer",
				PortB:       "transfer",
				Order:       "unordered",
				Version:     "ics20-1",
			},
			State: State{},
		},
	}
}

// steps to convert sovereign to consumer chain
func stepsChangeoverToConsumer(consumerName string) []Step {
	s := []Step{
		{
			Action: submitConsumerAdditionProposalAction{
				PreCCV:        true,
				Chain:         ChainID("provi"),
				From:          ValidatorID("alice"),
				Deposit:       10000001,
				ConsumerChain: ChainID(consumerName),
				// chain-0 is the transfer channelID that gets created in stepsSovereignTransferChan
				// the consumer chain will use this channel to send rewards to the provider chain
				// there is no need to create a new channel for rewards distribution
				DistributionChannel: "channel-0",
				SpawnTime:           0,
				InitialHeight:       clienttypes.Height{RevisionNumber: 0, RevisionHeight: 111}, // 1 block after upgrade !important
			},
			State: State{
				ChainID("provi"): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9489999999,
						ValidatorID("bob"):   9500000000,
					},
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         ChainID(consumerName),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 111},
							Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
						},
					},
				},
			},
		},
		{
			Action: voteGovProposalAction{
				Chain:      ChainID("provi"),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol")},
				Vote:       []string{"yes", "yes", "yes"},
				PropNumber: 1,
			},
			State: State{
				ChainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         ChainID(consumerName),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 111},
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9500000000,
						ValidatorID("bob"):   9500000000,
					},
				},
			},
		},
		{
			Action: ChangeoverChainAction{
				SovereignChain: ChainID(consumerName),
				ProviderChain:  ChainID("provi"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("alice"), Stake: 500000000, Allocation: 10000000000},
					{Id: ValidatorID("bob"), Stake: 500000000, Allocation: 10000000000},
					{Id: ValidatorID("carol"), Stake: 500000000, Allocation: 10000000000},
				},
				GenesisChanges: ".app_state.ccvconsumer.params.soft_opt_out_threshold = \"0.05\"",
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// uses val powers from consumer
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: addIbcConnectionAction{
				ChainA:  ChainID(consumerName),
				ChainB:  ChainID("provi"),
				ClientA: 1,
				ClientB: 1,
			},
			State: State{},
		},
		{
			Action: addIbcChannelAction{
				ChainA:      ChainID(consumerName),
				ChainB:      ChainID("provi"),
				ConnectionA: 1,
				PortA:       "consumer",
				PortB:       "provider",
				Order:       "ordered",
			},
			State: State{},
		},
	}

	return s
}

// start sovereign chain with a single validator so it is easier to manage
// when the chain is converted to a consumer chain the validators from the
// consumer chain will be used
// validatoralice is the only validator on the sovereign chain that is in both
// sovereign validator set and consumer validator set
func stepRunSovereignChain() []Step {
	return []Step{
		{
			Action: StartSovereignChainAction{
				Chain: ChainID("sover"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("alice"), Stake: 500000000, Allocation: 10000000000},
				},
			},
			State: State{
				ChainID("sover"): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9500000000,
					},
				},
			},
		},
		{
			Action: delegateTokensAction{
				Chain:  ChainID("sover"),
				From:   ValidatorID("alice"),
				To:     ValidatorID("alice"),
				Amount: 11000000,
			},
			State: State{
				ChainID("sover"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   0, // does not exist on pre-ccv sover
						ValidatorID("carol"): 0, // does not exist on pre-ccv sover
					},
				},
			},
		},
	}
}

// TODO: use args instead of hardcoding
func stepsUpgradeChain() []Step {
	return []Step{
		{
			Action: LegacyUpgradeProposalAction{
				ChainID:       ChainID("sover"),
				UpgradeTitle:  "sovereign-changeover",
				Proposer:      ValidatorID("alice"),
				UpgradeHeight: 110,
			},
			State: State{
				ChainID("sover"): ChainState{
					Proposals: &map[uint]Proposal{
						1: UpgradeProposal{
							Title:         "sovereign-changeover",
							UpgradeHeight: 110,
							Type:          "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal",
							Deposit:       10000000,
							Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
						},
					},
				},
			},
		},
		{
			Action: voteGovProposalAction{
				Chain:      ChainID("sover"),
				From:       []ValidatorID{ValidatorID("alice")},
				Vote:       []string{"yes"},
				PropNumber: 1,
			},
			State: State{
				ChainID("sover"): ChainState{
					Proposals: &map[uint]Proposal{
						1: UpgradeProposal{
							Deposit:       10000000,
							UpgradeHeight: 110,
							Title:         "sovereign-changeover",
							Type:          "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal",
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
				},
			},
		},
		{
			Action: waitUntilBlockAction{
				Chain: ChainID("sover"),
				Block: 110,
			},
			State: State{},
		},
	}
}

// stepsPostChangeoverDelegate tests basic delegation and resulting validator power changes after changeover
// we cannot use stepsDelegate and stepsUnbond because they make assumptions about which connection to use
// here we need to use connection-1, and in tests with new consumers connection-0 is used because the chain is new (has no IBC states prior to launch)
func stepsPostChangeoverDelegate(consumerName string) []Step {
	return []Step{
		{
			Action: SendTokensAction{
				Chain:  ChainID(consumerName),
				From:   ValidatorID("alice"),
				To:     ValidatorID("bob"),
				Amount: 100,
			},
			State: State{
				ChainID(consumerName): ChainState{
					// Tx should not go through, ICS channel is not setup until first VSC packet has been relayed to consumer
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("bob"): 0,
					},
				},
			},
		},
		{
			Action: delegateTokensAction{
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
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 1,
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
				Amount: 100,
			},
			State: State{
				ChainID(consumerName): ChainState{
					// Tx should go through, ICS channel is setup
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("bob"): 100,
					},
				},
			},
		},
		{
			Action: unbondTokensAction{
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
				ChainID(consumerName): ChainState{
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
			Action: relayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID(consumerName),
				Port:    "provider",
				Channel: 1,
			},
			State: State{
				ChainID(consumerName): ChainState{
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
