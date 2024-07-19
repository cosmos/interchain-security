package main

import (
	"strconv"

	gov "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
)

// stepsInactiveValidatorsOnConsumer tests situations where validators that are *not* in the active set on the
// provider chain validate on the consumer chain.
// The provider chain is set to have at most *2* validators active in consensus, and there are 3 validators in total.
// high-level, this test does:
// - start the provider chain
// - start a consumer chain
// - check that non-consensus validators do not get slashed for downtime on the provider; and that they don't get rewards
// - check that active validators *do* get slashed for downtime on the provider, and don't get rewards while they are down
// - check that non-consensus validators *do* get jailed for downtime on consumer chains
// - check that non-consensus validators *become* consensus validators when they have enough power
func stepsInactiveProviderValidators() []Step {
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
							IsIncrementalReward: true, // we need to get incremental rewards
							// if we would look at total rewards, alice would trivially also get rewards,
							// because she gets rewards in the first block due to being in the genesis
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
					Amount: 700000000, // carol needs to have more than 2/3rds of power(alice) + power(carol) + power(bob) to run both chains alone, so we stake some more to her
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0,
							ValidatorID("bob"):   200,
							ValidatorID("carol"): 1000,
						},
						StakedTokens: &map[ValidatorID]uint{
							ValidatorID("alice"): 100000000,
							ValidatorID("bob"):   200000000,
							ValidatorID("carol"): 1000000000,
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
							ValidatorID("carol"): 1000,
						},
						StakedTokens: &map[ValidatorID]uint{
							ValidatorID("alice"): 100000000,
							ValidatorID("bob"):   198000000, // 1% slash
							ValidatorID("carol"): 1000000000,
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
							ValidatorID("carol"): 1000,
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
							ValidatorID("carol"): 1000,
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
							ValidatorID("carol"): 1000,
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
							ValidatorID("carol"): 1000,
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
							ValidatorID("carol"): 1000,
						},
					},
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 0, // alice is not consensus-active anyways, since we allow two vals at maximum
							ValidatorID("bob"):   198,
							ValidatorID("carol"): 1000,
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
							ValidatorID("alice"): 0, // alice is still not in the active set, and should now be jailed too.
							// we cannot test directly whether alice is jailed, but we will test this below
							ValidatorID("bob"):   198,
							ValidatorID("carol"): 1000,
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
							ValidatorID("carol"): 1000,
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
							ValidatorID("carol"): 1000,
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
							// alice was not slashed because consumer downtime just jails without slashing tokens
							ValidatorID("alice"): 100, // alice is back as an active consensus validator.
							ValidatorID("bob"):   0,   // bob is still jailed
							ValidatorID("carol"): 1000,
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
							ValidatorID("carol"): 1000,
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
							ValidatorID("carol"): 1000,
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
							Status:        strconv.Itoa(int(gov.ProposalStatus_PROPOSAL_STATUS_VOTING_PERIOD)),
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
		// Οpt in all validators
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
			Action: OptInAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("carol"),
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
							Status:        strconv.Itoa(int(gov.ProposalStatus_PROPOSAL_STATUS_PASSED)),
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
						ValidatorID("carol"): 300,
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
	}
}

func stepsInactiveValsWithTopN() []Step {
	return []Step{
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
						IsIncrementalReward: true, // we need to get incremental rewards
						// if we would look at total rewards, alice would trivially also get rewards,
						// because she gets rewards in the first block due to being in the genesis
						IsRewarded: map[ValidatorID]bool{
							ValidatorID("alice"): false,
							ValidatorID("bob"):   true,
							ValidatorID("carol"): true,
						},
					},
				},
			},
		},
		{
			Action: SubmitConsumerAdditionProposalAction{
				Chain:         ChainID("provi"),
				From:          ValidatorID("alice"),
				Deposit:       10000001,
				ConsumerChain: ChainID("consu"),
				SpawnTime:     0,
				InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
				TopN:          51,
			},
			State: State{
				ChainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         ChainID("consu"),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        strconv.Itoa(int(gov.ProposalStatus_PROPOSAL_STATUS_VOTING_PERIOD)),
						},
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
							Status:        strconv.Itoa(int(gov.ProposalStatus_PROPOSAL_STATUS_PASSED)),
						},
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {},
						ValidatorID("bob"):   {}, // bob doesn't have to validate because he is not in the top N
						ValidatorID("carol"): {"consu"},
					},
				},
			},
		},
		{
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
						ValidatorID("carol"): 300,
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
	}
}
