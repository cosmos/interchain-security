package main

import clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"

// stepsOptInChain starts a provider chain and an Opt-In chain and opts in and out validators
// high-level, this test does:
// - start the provider chain
// - start a consumer chain
// - check that non-consensus validators do not get slashed for downtime; and that they don't get rewards
// - check that active validators *do* get slashed for downtime, and don't get rewards while they are down
// - check that non-consensus validators *do* get jailed for downtime on consumer chains
// - check that non-consensus validators *become* consensus validators when they have enough power
func stepsInactiveValidatorsOnConsumer() []Step {
	s := concatSteps(
		[]Step{
			{
				Action: StartChainAction{
					Chain: ChainID("provi"),
					Validators: []StartChainValidator{
						{Id: ValidatorID("alice"), Stake: 100000000, Allocation: 10000000000},
						{Id: ValidatorID("bob"), Stake: 200000000, Allocation: 10000000000},
						{Id: ValidatorID("carol"), Stake: 300000000, Allocation: 10000000000},
					},
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0, // max consensus validators is 2, so alice should not be in power
							ValidatorID("bob"):   200,
							ValidatorID("carol"): 300,
						},
						StakedTokens: &map[ValidatorID]uint{
							ValidatorID("alice"): 100000000,
							ValidatorID("bob"):   200000000,
							ValidatorID("carol"): 300000000,
						},
						Rewards: &Rewards{
							IsNativeDenom:       true, // check for rewards in the provider denom
							IsIncrementalReward: true, // check current rewards, because alice gets one block of rewards due to being in the genesis
							IsRewarded: map[ValidatorID]bool{
								ValidatorID("alice"): false,
								ValidatorID("bob"):   true,
								ValidatorID("carol"): true,
							},
						},
					},
				},
			},
		},
		setupOptInChain(),
		[]Step{
			// check that active-but-not-consensus validators do not get slashed for downtime
			{
				// alices provider node goes offline
				Action: DowntimeSlashAction{
					Chain:     ChainID("provi"),
					Validator: ValidatorID("alice"),
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0, // still 0 consensus power
							ValidatorID("bob"):   200,
							ValidatorID("carol"): 300,
						},
						StakedTokens: &map[ValidatorID]uint{
							ValidatorID("alice"): 100000000, // but alice does not get jailed or slashed
							ValidatorID("bob"):   200000000,
							ValidatorID("carol"): 300000000,
						},
					},
				},
			},
			// give carol more power so that she has enough power to validate if bob goes down
			{
				Action: DelegateTokensAction{
					Chain:  ChainID("provi"),
					From:   ValidatorID("carol"),
					To:     ValidatorID("carol"),
					Amount: 200000000, // carol needs to have more than 2/3rds of power(carol) + power(bob), so if bob has 200 power, carol needs at least 401, so we just go for 500
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0,
							ValidatorID("bob"):   200,
							ValidatorID("carol"): 500,
						},
						StakedTokens: &map[ValidatorID]uint{
							ValidatorID("alice"): 100000000,
							ValidatorID("bob"):   200000000,
							ValidatorID("carol"): 500000000,
						},
						// check that bob and carol get rewards, but alice does not
						Rewards: &Rewards{
							IsNativeDenom:       true, // check for rewards in the provider denom
							IsIncrementalReward: true, // check rewards since block 1
							IsRewarded: map[ValidatorID]bool{
								ValidatorID("alice"): false,
								ValidatorID("bob"):   true,
								ValidatorID("carol"): true,
							},
						},
					},
				},
			},
			// bob goes offline
			{
				Action: DowntimeSlashAction{
					Chain:     ChainID("provi"),
					Validator: ValidatorID("bob"),
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100, // alice gets into the active set
							ValidatorID("bob"):   0,   // bob is jailed
							ValidatorID("carol"): 500,
						},
						StakedTokens: &map[ValidatorID]uint{
							ValidatorID("alice"): 100000000,
							ValidatorID("bob"):   198000000, // 1% slash
							ValidatorID("carol"): 500000000,
						},
					},
				},
			},
			{
				// relay packets so that the consumer gets up to date with the provider
				Action: RelayPacketsAction{
					ChainA:  ChainID("provi"),
					ChainB:  ChainID("consu"),
					Port:    "provider",
					Channel: 0,
				},
				State: State{
					ChainID("provi"): ChainState{
						// check that now every validator got rewarded since the first block
						Rewards: &Rewards{
							IsNativeDenom:       true, // check for rewards in the provider denom
							IsIncrementalReward: true, // check rewards for currently produced blocks only
							IsRewarded: map[ValidatorID]bool{
								ValidatorID("alice"): true,  // alice is participating right now, so gets rewards
								ValidatorID("bob"):   false, // bob does not get rewards since he is not participating in consensus
								ValidatorID("carol"): true,
							},
						},
					},
					ChainID("consu"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100,
							ValidatorID("bob"):   0,
							ValidatorID("carol"): 500,
						},
					},
				},
			},
			// unjail bob
			{
				Action: UnjailValidatorAction{
					Provider:  ChainID("provi"),
					Validator: ValidatorID("bob"),
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0,   // alice is back out because only 2 validators can be active in consensus
							ValidatorID("bob"):   198, // bob was slashed 1%
							ValidatorID("carol"): 500,
						},
						// check that between two blocks now, alice does not get rewarded with the native denom
						Rewards: &Rewards{
							IsNativeDenom:       true, // check for rewards in the provider denom
							IsIncrementalReward: true, // check rewards for currently produced blocks only
							IsRewarded: map[ValidatorID]bool{
								ValidatorID("alice"): false,
								ValidatorID("bob"):   true,
								ValidatorID("carol"): true,
							},
						},
					},
					// bob is still at 0 power on the consumer chain
					ChainID("consu"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100,
							ValidatorID("bob"):   0,
							ValidatorID("carol"): 500,
						},
					},
				},
			},
			// relay packets so that the consumer gets up to date with the provider
			{
				Action: RelayPacketsAction{
					ChainA:  ChainID("provi"),
					ChainB:  ChainID("consu"),
					Port:    "provider",
					Channel: 0,
				},
				State: State{
					ChainID("consu"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100,
							ValidatorID("bob"):   198,
							ValidatorID("carol"): 500,
						},
					},
				},
			},
			// alice goes offline on the consumer chain
			{
				Action: DowntimeSlashAction{
					Chain:     ChainID("consu"),
					Validator: ValidatorID("alice"),
				},
				State: State{
					ChainID("consu"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100, // power not affected yet
							ValidatorID("bob"):   198,
							ValidatorID("carol"): 500,
						},
					},
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0, // alice is not consensus-active anyways, since we allow two vals at maximum
							ValidatorID("bob"):   198,
							ValidatorID("carol"): 500,
						},
					},
				},
			},
			// relay the packets so that the provider chain knows about alice's downtime
			{
				Action: RelayPacketsAction{
					ChainA:  ChainID("consu"),
					ChainB:  ChainID("provi"),
					Port:    "consumer",
					Channel: 0,
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0, // alice is still not in the active set, and should now be jailed too
							ValidatorID("bob"):   198,
							ValidatorID("carol"): 500,
						},
					},
				},
			},
			// we need to double-check that alice is actually jailed, so we get bob jailed, too, which usually would mean alice gets into power
			{
				Action: DowntimeSlashAction{
					Chain:     ChainID("provi"),
					Validator: ValidatorID("bob"),
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0, // alice is jailed
							ValidatorID("bob"):   0, // bob is jailed
							ValidatorID("carol"): 500,
						},
					},
				},
			},
			// relay the packets so that the consumer chain is in sync again
			{
				Action: RelayPacketsAction{
					ChainA:  ChainID("provi"),
					ChainB:  ChainID("consu"),
					Port:    "provider",
					Channel: 0,
				},
				State: State{
					ChainID("consu"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0, // alice is jailed
							ValidatorID("bob"):   0, // bob is jailed
							ValidatorID("carol"): 500,
						},
					},
					ChainID("provi"): ChainState{
						// check that alice and bob don't get consumer rewards
						Rewards: &Rewards{
							IsNativeDenom:       false, // check for rewards from consumer
							IsIncrementalReward: true,  // check rewards for currently produced blocks only
							IsRewarded: map[ValidatorID]bool{
								ValidatorID("alice"): false,
								ValidatorID("bob"):   false,
								ValidatorID("carol"): true,
							},
						},
					},
				},
			},

			// unjail alice
			{
				Action: UnjailValidatorAction{
					Provider:  ChainID("provi"),
					Validator: ValidatorID("alice"),
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100, // alice is back as an active consensus validator
							ValidatorID("bob"):   0,   // bob is still jailed
							ValidatorID("carol"): 500,
						},
					},
				},
			},
			// unjail bob
			{
				Action: UnjailValidatorAction{
					Provider:  ChainID("provi"),
					Validator: ValidatorID("bob"),
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0,   // alice is back out because only 2 validators can be active in consensus
							ValidatorID("bob"):   196, // bob is back as an active consensus validator and lost 2 more power due to the second downtime
							ValidatorID("carol"): 500,
						},
					},
				},
			},
			// relay the packets so that the consumer chain is in sync again
			{
				Action: RelayPacketsAction{
					ChainA:  ChainID("provi"),
					ChainB:  ChainID("consu"),
					Port:    "provider",
					Channel: 0,
				},
				State: State{
					ChainID("consu"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100, // both alice and bob are validating the consumer
							ValidatorID("bob"):   196,
							ValidatorID("carol"): 500,
						},
					},
				},
			},
		},
	)

	return s
}

// Precondition: The provider chain is running.
// Postcondition: A consumer chain with Top N = 0 is running, including an up-and-running IBC connection to the provider.
// "alice", "bob", "carol" have opted in and are validating.
func setupOptInChain() []Step {
	return []Step{
		{
			Action: SubmitConsumerAdditionProposalAction{
				Chain:         ChainID("provi"),
				From:          ValidatorID("alice"),
				Deposit:       10000001,
				ConsumerChain: ChainID("consu"),
				SpawnTime:     0,
				InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
				TopN:          0,
			},
			State: State{
				ChainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         ChainID("consu"),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
						},
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {},
						ValidatorID("bob"):   {},
						ValidatorID("carol"): {},
					},
				},
			},
		},
		// Οpt in "alice" and "bob" so the chain is not empty when it is about to start. Note, that "alice" and "bob" use
		// the provider's public key (see `UseConsumerKey` is set to `false` in `getDefaultValidators`) and hence do not
		// need a consumer-key assignment.
		{
			Action: OptInAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("alice"),
			},
			State: State{
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {}, // chain is not running yet
						ValidatorID("bob"):   {},
						ValidatorID("carol"): {},
					},
				},
			},
		},
		{
			Action: OptInAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("bob"),
			},
			State: State{
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {},
						ValidatorID("bob"):   {},
						ValidatorID("carol"): {},
					},
				},
			},
		},
		{
			Action: VoteGovProposalAction{
				Chain:      ChainID("provi"),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob")},
				Vote:       []string{"yes", "yes"},
				PropNumber: 1,
			},
			State: State{
				ChainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         ChainID("consu"),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
				},
			},
		},
		{
			// we start all the validators but only "alice" and "bob" have opted in and hence
			// only "alice" and "bob" are validating blocks
			Action: StartConsumerChainAction{
				ConsumerChain: ChainID("consu"),
				ProviderChain: ChainID("provi"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("alice"), Stake: 100000000, Allocation: 10000000000},
					{Id: ValidatorID("bob"), Stake: 200000000, Allocation: 10000000000},
					{Id: ValidatorID("carol"), Stake: 300000000, Allocation: 10000000000},
				},
				// For consumers that're launching with the provider being on an earlier version
				// of ICS before the soft opt-out threshold was introduced, we need to set the
				// soft opt-out threshold to 0.05 in the consumer genesis to ensure that the
				// consumer binary doesn't panic. Sdk requires that all params are set to valid
				// values from the genesis file.
				GenesisChanges: ".app_state.ccvconsumer.params.soft_opt_out_threshold = \"0.05\"",
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						// carol has not yet opted in
						ValidatorID("carol"): 0,
					},
				},
			},
		},
		{
			Action: AddIbcConnectionAction{
				ChainA:  ChainID("consu"),
				ChainB:  ChainID("provi"),
				ClientA: 0,
				ClientB: 0,
			},
			State: State{},
		},
		{
			Action: AddIbcChannelAction{
				ChainA:      ChainID("consu"),
				ChainB:      ChainID("provi"),
				ConnectionA: 0,
				PortA:       "consumer",
				PortB:       "provider",
				Order:       "ordered",
			},
			State: State{},
		},
		{
			Action: OptInAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("carol"),
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						// "carol" has opted in, but the VSCPacket capturing the opt-in was not relayed yet
						ValidatorID("carol"): 0,
					},
				},
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
					},
				},
			},
		},
		{
			// assign the consumer key "carol" is using on the consumer chain to be the one "carol" uses when opting in
			Action: AssignConsumerPubKeyAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("carol"),
				// reconfigure the node -> validator was using provider key
				// until this point -> key matches config.consumerValPubKey for "carol"
				ConsumerPubkey:  getDefaultValidators()[ValidatorID("carol")].ConsumerValPubKey,
				ReconfigureNode: true,
			},
			State: State{},
		},
		{
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID("consu"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						// carol has now opted in
						ValidatorID("carol"): 300,
					},
				},
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
					},
				},
			},
		},
	}
}
