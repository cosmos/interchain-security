package main

// Compatibility steps comprise a reduced set of actions suited to perform
// sanity checks across different ICS versions.

import (
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
)

func compstepStartProviderChain() []Step {
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

func compstepsStartConsumerChain(consumerName string, proposalIndex, chainIndex uint, setupTransferChans bool) []Step {
	s := []Step{
		{
			Action: SubmitConsumerAdditionProposalAction{
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
					// not supported across major versions
					// ProposedConsumerChains: &[]string{consumerName},
				},
			},
		},
		// add a consumer key before the chain starts
		// the key will be present in consumer genesis initial_val_set
		{
			Action: AssignConsumerPubKeyAction{
				Chain:          ChainID(consumerName),
				Validator:      ValidatorID("carol"),
				ConsumerPubkey: getDefaultValidators()[ValidatorID("carol")].ConsumerValPubKey,
				// consumer chain has not started
				// we don't need to reconfigure the node
				// since it will start with consumer key
				ReconfigureNode: false,
			},
			State: State{
				ChainID(consumerName): ChainState{
					AssignedKeys: &map[ValidatorID]string{
						ValidatorID("carol"): getDefaultValidators()[ValidatorID("carol")].ConsumerValconsAddressOnProvider,
					},
					ProviderKeys: &map[ValidatorID]string{
						ValidatorID("carol"): getDefaultValidators()[ValidatorID("carol")].ValconsAddress,
					},
				},
			},
		},
		{
			// op should fail - key already assigned by the same validator
			Action: AssignConsumerPubKeyAction{
				Chain:           ChainID(consumerName),
				Validator:       ValidatorID("carol"),
				ConsumerPubkey:  getDefaultValidators()[ValidatorID("carol")].ConsumerValPubKey,
				ReconfigureNode: false,
				ExpectError:     true,
				ExpectedError:   "a validator has assigned the consumer key already: consumer key is already in use by a validator",
			},
			State: State{},
		},
		{
			// op should fail - key already assigned by another validator
			Action: AssignConsumerPubKeyAction{
				Chain:     ChainID(consumerName),
				Validator: ValidatorID("bob"),
				// same pub key as carol
				ConsumerPubkey:  getDefaultValidators()[ValidatorID("carol")].ConsumerValPubKey,
				ReconfigureNode: false,
				ExpectError:     true,
				ExpectedError:   "a validator has assigned the consumer key already: consumer key is already in use by a validator",
			},
			State: State{
				ChainID(consumerName): ChainState{
					AssignedKeys: &map[ValidatorID]string{
						ValidatorID("carol"): getDefaultValidators()[ValidatorID("carol")].ConsumerValconsAddressOnProvider,
						ValidatorID("bob"):   "",
					},
					ProviderKeys: &map[ValidatorID]string{
						ValidatorID("carol"): getDefaultValidators()[ValidatorID("carol")].ValconsAddress,
					},
				},
			},
		},
		{
			Action: VoteGovProposalAction{
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
				},
			},
		},
		{
			Action: StartConsumerChainAction{
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
					// not supported
					// ProposedConsumerChains: &[]string{},
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
			Action: AddIbcConnectionAction{
				ChainA:  ChainID(consumerName),
				ChainB:  ChainID("provi"),
				ClientA: 0,
				ClientB: chainIndex,
			},
			State: State{},
		},
		{
			Action: AddIbcChannelAction{
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
			Action: TransferChannelCompleteAction{
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
func compstepsStartChains(consumerNames []string, setupTransferChans bool) []Step {
	s := compstepStartProviderChain()
	for i, consumerName := range consumerNames {
		s = append(s, compstepsStartConsumerChain(consumerName, uint(i+1), uint(i), setupTransferChans)...)
	}

	return s
}
