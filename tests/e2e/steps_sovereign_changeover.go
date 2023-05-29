package main

import clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"

func stepsChangeoverConsumerChain(consumerName string, proposalIndex, chainIndex uint, setupTransferChans bool) []Step {
	s := []Step{
		{
			action: submitConsumerAdditionProposalAction{
				chain:         chainID("provi"),
				from:          validatorID("alice"),
				deposit:       10000001,
				consumerChain: chainID(consumerName),
				spawnTime:     0,
				initialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9489999999,
						validatorID("bob"):   9500000000,
					},
					Proposals: &map[uint]Proposal{
						proposalIndex: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         chainID(consumerName),
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
			action: assignConsumerPubKeyAction{
				chain:          chainID(consumerName),
				validator:      validatorID("carol"),
				consumerPubkey: `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
				// consumer chain has not started
				// we don't need to reconfigure the node
				// since it will start with consumer key
				reconfigureNode: false,
			},
			state: State{
				chainID(consumerName): ChainState{
					AssignedKeys: &map[validatorID]string{
						validatorID("carol"): "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
					},
					ProviderKeys: &map[validatorID]string{
						validatorID("carol"): "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
					},
				},
			},
		},
		{
			// op should fail - key already assigned by the same validator
			action: assignConsumerPubKeyAction{
				chain:           chainID(consumerName),
				validator:       validatorID("carol"),
				consumerPubkey:  `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
				reconfigureNode: false,
				expectError:     true,
			},
			state: State{},
		},
		{
			// op should fail - key already assigned by another validator
			action: assignConsumerPubKeyAction{
				chain:     chainID(consumerName),
				validator: validatorID("bob"),
				// same pub key as carol
				consumerPubkey:  `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
				reconfigureNode: false,
				expectError:     true,
			},
			state: State{
				chainID(consumerName): ChainState{
					AssignedKeys: &map[validatorID]string{
						validatorID("carol"): "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
						validatorID("bob"):   "",
					},
					ProviderKeys: &map[validatorID]string{
						validatorID("carol"): "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
					},
				},
			},
		},
		{
			action: voteGovProposalAction{
				chain:      chainID("provi"),
				from:       []validatorID{validatorID("alice"), validatorID("bob"), validatorID("carol")},
				vote:       []string{"yes", "yes", "yes"},
				propNumber: proposalIndex,
			},
			state: State{
				chainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						proposalIndex: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         chainID(consumerName),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9500000000,
					},
				},
			},
		},
		{
			action: changeoverChainAction{
				providerChain: chainID("provi"),
				validators: []StartChainValidator{
					{id: validatorID("bob"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("carol"), stake: 500000000, allocation: 10000000000},
				},
				// For consumers that're launching with the provider being on an earlier version
				// of ICS before the soft opt-out threshold was introduced, we need to set the
				// soft opt-out threshold to 0.05 in the consumer genesis to ensure that the
				// consumer binary doesn't panic. Sdk requires that all params are set to valid
				// values from the genesis file.
				genesisChanges: ".app_state.ccvconsumer.params.soft_opt_out_threshold = \"0.05\"",
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9500000000,
						validatorID("carol"): 9500000000,
					},
				},
				chainID(consumerName): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 10000000000,
						validatorID("bob"):   10000000000,
						validatorID("carol"): 10000000000,
					},
				},
			},
		},
		{
			action: addIbcConnectionAction{
				chainA:  chainID(consumerName),
				chainB:  chainID("provi"),
				clientA: 0,
				clientB: chainIndex,
			},
			state: State{},
		},
		{
			action: addIbcChannelAction{
				chainA:      chainID(consumerName),
				chainB:      chainID("provi"),
				connectionA: 0,
				portA:       "consumer", // TODO: check port mapping
				portB:       "provider",
				order:       "ordered",
			},
			state: State{},
		},
	}

	// currently only used in democracy tests
	if setupTransferChans {
		s = append(s, Step{
			action: transferChannelCompleteAction{
				chainA:      chainID(consumerName),
				chainB:      chainID("provi"),
				connectionA: 0,
				portA:       "transfer",
				portB:       "transfer",
				order:       "unordered",
				channelA:    1,
				channelB:    1,
			},
			state: State{},
		})
	}
	return s
}
