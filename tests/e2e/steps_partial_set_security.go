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
		// need a consumer-key assigment.
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
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {},
						ValidatorID("carol"): {"consu"},
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
						// "bob" has not yet been opted in to the consumer chain because the VSCPacket has not yet been relayed
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 300,
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"}, // but has to validate is true because bob opted in on the provider
						ValidatorID("carol"): {"consu"},
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
						// bob is in power on the consumer
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
				},
			},
		},
		{
			// DowntimeSlash for alice on consumer
			Action: DowntimeSlashAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("alice"),
			},
			// powers are not affected yet on either chain
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
				},
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
					},
				},
			},
		},
		{
			// relay the slash packet
			Action: RelayPacketsAction{
				ChainA:  ChainID("consu"),
				ChainB:  ChainID("provi"),
				Port:    "consumer",
				Channel: 0,
			},
			// alice's power is reduced on the provider
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {}, // alice is jailed on the provider and does not have to validate
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
					},
				},
			},
		},
		{
			// relay the VSCPacket that contains the slashed power for alice
			Action: RelayPacketsAction{
				ChainA:  ChainID("consu"),
				ChainB:  ChainID("provi"),
				Port:    "consumer",
				Channel: 0,
			},
			// alice's power is reduced on the provider
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {}, // alice is jailed on the provider and does not have to validate
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
					},
				},
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// alice should definitely not be in power on the consumer
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
				},
			},
		},
		{
			// unjail alice
			Action: UnjailValidatorAction{
				Provider:  ChainID("provi"),
				Validator: ValidatorID("alice"),
			},
			// alices power is restored on the provider
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"}, // alice is unjailed and hence has to validate again
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
					},
				},
				// still 0 power on the consumer
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
				},
			},
		},
		{
			// relay the VSCPacket that puts alice back into power on the consumer
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID("consu"),
				Port:    "provider",
				Channel: 0,
			},
			// alice's power is restored on the consumer
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
			// slash alice for downtime again
			Action: DowntimeSlashAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("alice"),
			},
			// alice's power is not yet reduced, the packet needs to be relayed
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
				},
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
					},
				},
			},
		},
		{
			// relay the slash packet
			Action: RelayPacketsAction{
				ChainA:  ChainID("consu"),
				ChainB:  ChainID("provi"),
				Port:    "consumer",
				Channel: 0,
			},
			// alice's power is reduced on the provider
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {}, // alice is jailed on the provider and does not have to validate
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
					},
				},
			},
		},
		{
			// relay the VSCPacket that contains the slashed power for alice
			Action: RelayPacketsAction{
				ChainA:  ChainID("consu"),
				ChainB:  ChainID("provi"),
				Port:    "consumer",
				Channel: 0,
			},
			// alice's power is reduced on the consumer
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
				},
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   200,
						ValidatorID("carol"): 300,
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {}, // alice is jailed on the provider and does not have to validate
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
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
				Chain:       ChainID("consu"),
				Validator:   ValidatorID("carol"),
				ExpectError: true,
			},
			State: State{},
		},
		{
			Action: OptOutAction{
				Chain:       ChainID("consu"),
				Validator:   ValidatorID("bob"),
				ExpectError: true,
			},
			State: State{
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
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {}, // alice has opted out and the epoch is over, so definitely does not have to validate anymore
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
					},
				},
			},
		},
		// opt alice back in
		{
			Action: OptInAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("alice"),
			},
			State: State{
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"}, // alice has to validate again
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
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
						// "alice" has now opted in
						ValidatorID("alice"): 200,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
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
			// DowntimeSlash for alice on consumer
			Action: DowntimeSlashAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("alice"),
			},
			// powers are not affected yet on either chain
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 200,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
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
			// relay the slash packet
			Action: RelayPacketsAction{
				ChainA:  ChainID("consu"),
				ChainB:  ChainID("provi"),
				Port:    "consumer",
				Channel: 0,
			},
			// alice's power is reduced on the provider
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay the VSCPacket that contains the slashed power for alice
			Action: RelayPacketsAction{
				ChainA:  ChainID("consu"),
				ChainB:  ChainID("provi"),
				Port:    "consumer",
				Channel: 0,
			},
			// alice's power is reduced on the provider
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// alice should definitely not be in power on the consumer
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			// unjail alice
			Action: UnjailValidatorAction{
				Provider:  ChainID("provi"),
				Validator: ValidatorID("alice"),
			},
			// alices power is restored on the provider
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 200,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
				// still 0 power on the consumer
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
			// relay the VSCPacket that puts alice back into power on the consumer
			Action: RelayPacketsAction{
				ChainA:  ChainID("provi"),
				ChainB:  ChainID("consu"),
				Port:    "provider",
				Channel: 0,
			},
			// alice's power is restored on the consumer
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
			// slash alice for downtime again
			Action: DowntimeSlashAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("alice"),
			},
			// alice's power is not yet reduced, the packet needs to be relayed
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 200,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
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
			// relay the slash packet
			Action: RelayPacketsAction{
				ChainA:  ChainID("consu"),
				ChainB:  ChainID("provi"),
				Port:    "consumer",
				Channel: 0,
			},
			// alice's power is reduced on the provider
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
			},
		},
		{
			// relay the VSCPacket that contains the slashed power for alice
			Action: RelayPacketsAction{
				ChainA:  ChainID("consu"),
				ChainB:  ChainID("provi"),
				Port:    "consumer",
				Channel: 0,
			},
			// alice's power is reduced on the consumer
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   300,
						ValidatorID("carol"): 500,
					},
				},
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
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

// stepsValidatorSetCappedChain starts a provider chain and an Opt-In chain that is validator-set capped
func stepsValidatorSetCappedChain() []Step {
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
				// we can have at most 2 validators validating the consumer chain
				ValidatorSetCap: 2,
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
		// Οpt in "alice", "bob", and "carol." Note, that "alice" and "bob" use the provider's public key
		// (see `UseConsumerKey` is set to `false` in `getDefaultValidators`) and hence do not need a consumer-key assigment.
		{
			Action: OptInAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("alice"),
			},
			State: State{
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						// chain is not running yet and hence noone has to validate
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
						// alice does not validate because the consumer chain is validator-set capped to 2 validators and
						// bob and carol have more power than alice
						ValidatorID("alice"): 0,
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
		{
			Action: OptOutAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("carol"),
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   200,
						// "carol" has opted out, but the VSCPacket capturing the opt-out was not relayed yet
						ValidatorID("carol"): 300,
					},
				},
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {}, // "carol" does not have to validate anymore because it opted out
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
						// "alice" is now validating the consumer chain as well because the chain is capped to 2 validators
						// and "carol" just opted out
						ValidatorID("alice"): 100,
						ValidatorID("bob"):   200,
						// "carol" has now opted out
						ValidatorID("carol"): 0,
					},
				},
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {},
					},
				},
			},
		},
	}

	return s
}

// stepsValidatorsPowerCappedChain starts a provider chain and an Opt-In chain that is validators-power capped
func stepsValidatorsPowerCappedChain() []Step {
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
				// Set the power cap to 34%. No validator can have more than 34% of the voting power on the consumer chain
				ValidatorsPowerCap: 34,
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
		// Οpt in "alice", "bob", and "carol." Note, that "alice" and "bob" use the provider's public key
		// (see `UseConsumerKey` is set to `false` in `getDefaultValidators`) and hence do not need a consumer-key assigment.
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
						// the powers of the validators on the consumer chain are different from the provider chain
						// because the consumer chain is power capped. Note that the total power is 600 (= 194 + 203 + 203)
						// and 203 / 600.0 = 0.338 < 34% that is the power cap.
						ValidatorID("alice"): 194,
						ValidatorID("bob"):   203,
						ValidatorID("carol"): 203,
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
			Action: OptOutAction{
				Chain:     ChainID("consu"),
				Validator: ValidatorID("carol"),
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 194,
						ValidatorID("bob"):   203,
						ValidatorID("carol"): 203,
					},
				},
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {}, // "carol" does not have to validate anymore because it opted out
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
						// "carol" has opted out, and we only have 2 validators left validating. Power capping only operates
						// in a best-effort basis and with 2 validators we cannot guarantee that no validator has more
						// than 34% of the voting power. In this case, both validators get the same voting power (50% = 101 / 202).
						ValidatorID("alice"): 101,
						ValidatorID("bob"):   101,
						ValidatorID("carol"): 0,
					},
				},
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {},
					},
				},
			},
		},
	}

	return s
}

// stepsValidatorsAllowlistedChain starts a provider chain and an Opt-In chain with an allowlist
func stepsValidatorsAllowlistedChain() []Step {
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
				// only "alice" and "bob" are allowlisted (see `getDefaultValidators` in `tests/e2e/config.go`)
				Allowlist: []string{"cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
					"cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"},
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
		// Οpt in "alice", "bob", and "carol." Note, that "alice" and "bob" use the provider's public key
		// (see `UseConsumerKey` is set to `false` in `getDefaultValidators`) and hence do not need a consumer-key assigment.
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
						// "carol" is not allowlisted and hence does not validate the consumer chain
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
						ValidatorID("carol"): 0,
					},
				},
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {},
					},
				},
			},
		},
	}

	return s
}

// stepsValidatorsDenylistedChain starts a provider chain and an Opt-In chain with a denylist
func stepsValidatorsDenylistedChain() []Step {
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
				// only "bob" is allowlisted (see `getDefaultValidators` in `tests/e2e/config.go`)
				Denylist: []string{"cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"},
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
		// Οpt in "alice", "bob", and "carol." Note, that "alice" and "bob" use the provider's public key
		// (see `UseConsumerKey` is set to `false` in `getDefaultValidators`) and hence do not need a consumer-key assigment.
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
						// "bob" is denylisted and hence does not valiate the consumer chain
						ValidatorID("bob"):   0,
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
						ValidatorID("bob"):   0,
						ValidatorID("carol"): 300,
					},
				},
				ChainID("provi"): ChainState{
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {},
						ValidatorID("carol"): {"consu"},
					},
				},
			},
		},
	}

	return s
}
