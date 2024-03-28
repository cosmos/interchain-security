package main

import clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"

// stepsOptInChain starts a provider chain and an Opt-In chain and opts in and out validators
func stepsOptInChain() []Step {
	s := []Step{
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
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
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
				},
			},
		},
		// Οpt in "alice" and "bob" so the chain is not empty when it is about to start. Note, that "alice" and "bob" use
		// the provider's public key (see `UseConsumerKey` is set to `false` in `getDefaultValidators`) and hence do not
		// need a consumer-key assigment.
		{
			Action: OptInAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("alice"),
			},
			State: State{},
		},
		{
			Action: OptInAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("bob"),
			},
			State: State{},
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
						// "carol" has not yet opted in, the VSCPacket capturing the opt-in should first be relayed
						ValidatorID("carol"): 0,
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
				// until this point -> key matches config.consumerValPubKey for "bob"
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
			},
		},
		{
			Action: OptOutAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("bob"),
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						// "bob" has not yet opted out from the consumer chain because the VSCPacket has not yet been relayed
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
				},
			},
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
						// bob has now opted out
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 300,
					},
				},
			},
		},
		{
			// re opt-in "bob"
			Action: OptInAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("bob"),
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						// "bob" has not yet been opted in from the consumer chain because the VSCPacket has not yet been relayed
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 300,
					},
				},
			},
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
						// bob has now opted in
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
				},
			},
		},
	}

	return s
}

// stepsTopNChain starts a provider chain and a Top-N chain and opts in and out validators
func stepsTopNChain() []Step {
	s := []Step{
		{
			// start a new chain where "alice", "bob", and "carol" have 20%, 30%, and 50% of
			// the total voting power respectively
			Action: StartChainAction{
				Chain: ChainID("provi"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("alice"), Stake: 200000000, Allocation: 10000000000},
					{Id: ValidatorID("bob"), Stake: 300000000, Allocation: 10000000000},
					{Id: ValidatorID("carol"), Stake: 500000000, Allocation: 10000000000},
				},
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 200,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			// propose a Top-N chain with N = 51% and hence both "carol" and "bob" have to validate
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
							Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
						},
					},
				},
			},
		},
		{
			// change the consumer key "carol" is using on the consumer chain to be the one "carol" uses when opting in
			Action: AssignConsumerPubKeyAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("carol"),
				// reconfigure the node -> validator was using provider key
				// until this point -> key matches config.consumerValPubKey for "bob"
				ConsumerPubkey:  getDefaultValidators()[ValidatorID("carol")].ConsumerValPubKey,
				ReconfigureNode: true,
			},
			State: State{},
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
					{Id: ValidatorID("alice"), Stake: 200000000, Allocation: 10000000000},
					{Id: ValidatorID("bob"), Stake: 300000000, Allocation: 10000000000},
					{Id: ValidatorID("carol"), Stake: 500000000, Allocation: 10000000000},
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
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
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
				Validator: ValidatorID("alice"),
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// "alice" is not yet opted in because the VSCPacket has not yet been relayed
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
			},
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
						// "alice" is now opted in
						ValidatorID("alice"): 200,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: OptOutAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("carol"),
			},
			State: State{},
		},
		{
			Action: OptOutAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("bob"),
			},
			State: State{},
		},
		{
			// opting out "bob" or "carol" does not work because they belong to the Top N validators
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID("consu"),
				Port:    "provider",
				Channel: 0,
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 200,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			Action: OptOutAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("alice"),
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
						// "alice" has now opted out
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
	}

	return s
}
