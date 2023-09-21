package main

import (
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
)

func stepStartProviderChain() []Step {
	return []Step{
		{
			Action: StartChainAction{
				Chain: ChainID("provi"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("bob"), Stake: 500000000, Allocation: 10000000000},
					{Id: ValidatorID("alice"), Stake: 500000000, Allocation: 10000000000},
					{Id: ValidatorID("carol"), Stake: 500000000, Allocation: 10000000000},
				},
			},
			State: State{
				ChainID("provi"): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9500000000,
						ValidatorID("bob"):   9500000000,
						ValidatorID("carol"): 9500000000,
					},
				},
			},
		},
	}
}

func stepsStartConsumerChain(consumerName string, proposalIndex, chainIndex uint, setupTransferChans bool) []Step {
	s := []Step{
		{
			Action: submitConsumerAdditionProposalAction{
				Chain:         ChainID("provi"),
				From:          ValidatorID("alice"),
				Deposit:       10000001,
				ConsumerChain: ChainID(consumerName),
				SpawnTime:     0,
				InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
			},
			State: State{
				ChainID("provi"): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9489999999,
						ValidatorID("bob"):   9500000000,
					},
					Proposals: &map[uint]Proposal{
						proposalIndex: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         ChainID(consumerName),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
						},
					},
				},
			},
		},
		// add a consumer key before the chain starts
		// the key will be present in consumer genesis initial_val_set
		{
			Action: assignConsumerPubKeyAction{
				Chain:          ChainID(consumerName),
				Validator:      ValidatorID("carol"),
				ConsumerPubkey: `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
				// consumer chain has not started
				// we don't need to reconfigure the node
				// since it will start with consumer key
				ReconfigureNode: false,
			},
			State: State{
				ChainID(consumerName): ChainState{
					AssignedKeys: &map[ValidatorID]string{
						ValidatorID("carol"): "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
					},
					ProviderKeys: &map[ValidatorID]string{
						ValidatorID("carol"): "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
					},
				},
			},
		},
		{
			// op should fail - key already assigned by the same validator
			Action: assignConsumerPubKeyAction{
				Chain:           ChainID(consumerName),
				Validator:       ValidatorID("carol"),
				ConsumerPubkey:  `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
				ReconfigureNode: false,
				ExpectError:     true,
				ExpectedError:   "a validator has assigned the consumer key already: consumer key is already in use by a validator",
			},
			State: State{},
		},
		{
			// op should fail - key already assigned by another validator
			Action: assignConsumerPubKeyAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("bob"),
				// same pub key as carol
				ConsumerPubkey:  `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
				ReconfigureNode: false,
				ExpectError:     true,
				ExpectedError:   "a validator has assigned the consumer key already: consumer key is already in use by a validator",
			},
			State: State{
				ChainID(consumerName): ChainState{
					AssignedKeys: &map[ValidatorID]string{
						ValidatorID("carol"): "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
						ValidatorID("bob"):   "",
					},
					ProviderKeys: &map[ValidatorID]string{
						ValidatorID("carol"): "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
					},
				},
			},
		},
		{
			Action: voteGovProposalAction{
				Chain:      ChainID("provi"),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol")},
				Vote:       []string{"yes", "yes", "yes"},
				PropNumber: proposalIndex,
			},
			State: State{
				ChainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						proposalIndex: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         ChainID(consumerName),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9500000000,
						ValidatorID("bob"):   9500000000,
					},
					ProposedConsumerChains: &[]string{consumerName},
				},
			},
		},
		{
			Action: startConsumerChainAction{
				ConsumerChain: ChainID(consumerName),
				ProviderChain: ChainID("provi"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("bob"), Stake: 500000000, Allocation: 10000000000},
					{Id: ValidatorID("alice"), Stake: 500000000, Allocation: 10000000000},
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
				ChainID("provi"): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9500000000,
						ValidatorID("bob"):   9500000000,
						ValidatorID("carol"): 9500000000,
					},
					ProposedConsumerChains: &[]string{},
				},
				ChainID(consumerName): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 10000000000,
						ValidatorID("bob"):   10000000000,
						ValidatorID("carol"): 10000000000,
					},
				},
			},
		},
		{
			Action: addIbcConnectionAction{
				ChainA:  ChainID(consumerName),
				ChainB:  ChainID("provi"),
				ClientA: 0,
				ClientB: chainIndex,
			},
			State: State{},
		},
		{
			Action: addIbcChannelAction{
				ChainA:      ChainID(consumerName),
				ChainB:      ChainID("provi"),
				ConnectionA: 0,
				PortA:       "consumer", // TODO: check port mapping
				PortB:       "provider",
				Order:       "ordered",
			},
			State: State{},
		},
	}

	// currently only used in democracy tests
	if setupTransferChans {
		s = append(s, Step{
			Action: transferChannelCompleteAction{
				ChainA:      ChainID(consumerName),
				ChainB:      ChainID("provi"),
				ConnectionA: 0,
				PortA:       "transfer",
				PortB:       "transfer",
				Order:       "unordered",
				ChannelA:    1,
				ChannelB:    1,
			},
			State: State{},
		})
	}
	return s
}

// starts provider and consumer chains specified in consumerNames
// setupTransferChans will establish a channel for fee transfers between consumer and provider
func stepsStartChains(consumerNames []string, setupTransferChans bool) []Step {
	s := stepStartProviderChain()
	for i, consumerName := range consumerNames {
		s = append(s, stepsStartConsumerChain(consumerName, uint(i+1), uint(i), setupTransferChans)...)
	}

	return s
}

func stepsAssignConsumerKeyOnStartedChain(consumerName, validator string) []Step {
	return []Step{
		{
			Action: assignConsumerPubKeyAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("bob"),
				// reconfigure the node -> validator was using provider key
				// until this point -> key matches config.consumerValPubKey for "bob"
				ConsumerPubkey:  `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="}`,
				ReconfigureNode: true,
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// this happens after some delegations
						// so that the chain does not halt if 1/3 of power is offline
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// this happens after some delegations
						// so that the chain does not halt if 1/3 of power is offline
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
					AssignedKeys: &map[ValidatorID]string{
						ValidatorID("bob"):   "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
						ValidatorID("carol"): "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
					},
					ProviderKeys: &map[ValidatorID]string{
						ValidatorID("bob"):   "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
						ValidatorID("carol"): "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
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
						// this happens after some delegations
						// so that the chain does not halt if 1/3 of power is offline
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						// this happens after some delegations
						// so that the chain does not halt if 1/3 of power is offline
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   500,
						ValidatorID("carol"): 500,
					},
					AssignedKeys: &map[ValidatorID]string{
						ValidatorID("bob"):   "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
						ValidatorID("carol"): "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
					},
					ProviderKeys: &map[ValidatorID]string{
						ValidatorID("bob"):   "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
						ValidatorID("carol"): "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
					},
				},
			},
		},
	}
}
