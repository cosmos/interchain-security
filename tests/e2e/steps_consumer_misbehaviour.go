package main

import (
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
)

// starts a provider chain and a consumer chain with two validators,
// where the voting power is distributed in order that the smallest validator
// can soft opt-out of validating the consumer chain.
func stepsStartChainsWithSoftOptOut(consumerName string) []Step {
	s := []Step{
		{
			// Create a provider chain with two validators, where one validator holds 96% of the voting power
			// and the other validator holds 4% of the voting power.
			Action: StartChainAction{
				Chain: ChainID("provi"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("alice"), Stake: 500000000, Allocation: 10000000000},
					{Id: ValidatorID("bob"), Stake: 20000000, Allocation: 10000000000},
				},
			},
			State: State{
				ChainID("provi"): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9500000000,
						ValidatorID("bob"):   9980000000,
					},
				},
			},
		},
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
						ValidatorID("bob"):   9980000000,
					},
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
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
				Validator:      ValidatorID("alice"),
				ConsumerPubkey: `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="}`,
				// consumer chain has not started
				// we don't need to reconfigure the node
				// since it will start with consumer key
				ReconfigureNode: false,
			},
			State: State{
				ChainID(consumerName): ChainState{
					AssignedKeys: &map[ValidatorID]string{
						ValidatorID("alice"): "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
					},
					ProviderKeys: &map[ValidatorID]string{
						ValidatorID("alice"): "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
					},
				},
			},
		},
		{
			Action: voteGovProposalAction{
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
							Chain:         ChainID(consumerName),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 9500000000,
						ValidatorID("bob"):   9980000000,
					},
				},
			},
		},
		{
			// start a consumer chain using a single big validator knowing that it holds more than 2/3 of the voting power
			// and that the other validators hold less than 5% so they won't get jailed thanks to the sof opt-out mechanism.
			Action: startConsumerChainAction{
				ConsumerChain: ChainID(consumerName),
				ProviderChain: ChainID("provi"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("alice"), Stake: 500000000, Allocation: 10000000000},
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
						ValidatorID("bob"):   9980000000,
					},
				},
				ChainID(consumerName): ChainState{
					ValBalances: &map[ValidatorID]uint{
						ValidatorID("alice"): 10000000000,
					},
				},
			},
		},
		{
			Action: addIbcConnectionAction{
				ChainA:  ChainID(consumerName),
				ChainB:  ChainID("provi"),
				ClientA: 0,
				ClientB: 0,
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
		// delegate some token and relay the resulting VSC packets
		// in oder to initiates the CCV channel
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
						ValidatorID("bob"):   20,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 500,
						ValidatorID("bob"):   20,
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
						ValidatorID("bob"):   20,
					},
				},
			},
		},
	}

	return s
}

// stepsCauseConsumerMisbehaviour causes a ICS misbehaviour by forking a consumer chain.
func stepsCauseConsumerMisbehaviour(consumerName string) []Step {
	consumerClientID := "07-tendermint-0"
	forkRelayerConfig := "/root/.hermes/config_fork.toml"
	return []Step{
		{
			// fork the consumer chain by cloning the alice validator node
			Action: forkConsumerChainAction{
				ConsumerChain: ChainID(consumerName),
				ProviderChain: ChainID("provi"),
				Validator:     ValidatorID("alice"),
				RelayerConfig: forkRelayerConfig,
			},
			State: State{},
		},
		// start relayer to detect IBC misbehaviour
		{
			Action: startRelayerAction{},
			State:  State{},
		},
		// run Hermes relayer instance to detect the ICS misbehaviour
		// and jail alice on the provider
		{
			Action: startConsumerEvidenceDetectorAction{
				Chain: ChainID(consumerName),
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   20,
					},
					StakedTokens: &map[ValidatorID]uint{
						ValidatorID("alice"): 511000000,
						ValidatorID("bob"):   20000000,
					},
				},
				ChainID(consumerName): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   20,
					},
				},
			},
		},
		{
			// update the fork consumer client to create a light client attack
			// which should trigger a ICS misbehaviour message
			Action: updateLightClientAction{
				Chain:         ChainID(consumerName),
				ClientID:      consumerClientID,
				HostChain:     ChainID("provi"),
				RelayerConfig: forkRelayerConfig, // this relayer config uses the "forked" consumer
			},
			State: State{
				ChainID("provi"): ChainState{
					// alice should be jailed on the provider
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 0,
						ValidatorID("bob"):   20,
					},
					// "alice" should be slashed on the provider, hence representative
					// power is 511000000 - 0.05 * 511000000 = 485450000
					StakedTokens: &map[ValidatorID]uint{
						ValidatorID("alice"): 485450000,
						ValidatorID("bob"):   20000000,
					},
					// The consumer light client should be frozen on the provider
					ClientsFrozenHeights: &map[string]clienttypes.Height{
						consumerClientID: {
							RevisionNumber: 0,
							RevisionHeight: 1,
						},
					},
				},
				ChainID(consumerName): ChainState{
					// consumer should not have learned the jailing of alice
					// since its light client is frozen on the provider
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): 511,
						ValidatorID("bob"):   20,
					},
				},
			},
		},
	}
}
