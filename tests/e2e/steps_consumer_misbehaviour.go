package main

import (
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
)

// starts a provider chain and a consumer chain with two validators,
// where the voting power is distributed in order that the smallest validator
// can soft opt-out of validating the consumer chain.
func stepsStartChainsWithSoftOptOut(consumerName string) []Step {
	s := []Step{
		{
			// Create a provider chain with two validators, where one validator holds 96% of the voting power
			// and the other validator holds 4% of the voting power.
			action: StartChainAction{
				chain: chainID("provi"),
				validators: []StartChainValidator{
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("bob"), stake: 20000000, allocation: 10000000000},
				},
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9980000000,
					},
				},
			},
		},
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
						validatorID("bob"):   9980000000,
					},
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
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
				validator:      validatorID("alice"),
				consumerPubkey: `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="}`,
				// consumer chain has not started
				// we don't need to reconfigure the node
				// since it will start with consumer key
				reconfigureNode: false,
			},
			state: State{
				chainID(consumerName): ChainState{
					AssignedKeys: &map[validatorID]string{
						validatorID("alice"): "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
					},
					ProviderKeys: &map[validatorID]string{
						validatorID("alice"): "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
					},
				},
			},
		},
		{
			action: voteGovProposalAction{
				chain:      chainID("provi"),
				from:       []validatorID{validatorID("alice"), validatorID("bob")},
				vote:       []string{"yes", "yes"},
				propNumber: 1,
			},
			state: State{
				chainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         chainID(consumerName),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9980000000,
					},
				},
			},
		},
		{
			// start a consumer chain using a single big validator knowing that it holds more than 2/3 of the voting power
			// and that the other validators hold less than 5% so they won't get jailed thanks to the sof opt-out mechanism.
			action: startConsumerChainAction{
				consumerChain: chainID(consumerName),
				providerChain: chainID("provi"),
				validators: []StartChainValidator{
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
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
						validatorID("bob"):   9980000000,
					},
				},
				chainID(consumerName): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 10000000000,
					},
				},
			},
		},
		{
			action: addIbcConnectionAction{
				chainA:  chainID(consumerName),
				chainB:  chainID("provi"),
				clientA: 0,
				clientB: 0,
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
		// delegate some token and relay the resulting VSC packets
		// in oder to initiates the CCV channel
		{
			action: delegateTokensAction{
				chain:  chainID("provi"),
				from:   validatorID("alice"),
				to:     validatorID("alice"),
				amount: 11000000,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   20,
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 500,
						validatorID("bob"):   20,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chainA:  chainID("provi"),
				chainB:  chainID(consumerName),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   20,
					},
				},
			},
		},
	}

	return s
}

// stepsCauseConsumerMisbehaviour causes a consumer chain to misbehave by creating a fork,
// and relays the light client attack evidence to the provider
func stepsCauseConsumerMisbehaviour(consumerName string) []Step {
	consumerClientID := "07-tendermint-0"
	forkRelayerConfig := "/root/.hermes/config_fork.toml"

	return []Step{
		{
			action: forkConsumerChainAction{
				consumerChain: chainID(consumerName),
				providerChain: chainID("provi"),
				validator:     validatorID("alice"),
				relayerConfig: forkRelayerConfig,
			},
			state: State{},
		},
		{
			action: startRelayerAction{},
			state: State{
				// The consumer client shouldn't be frozen on the provider yet since
				// no client update packet was sent by the fork yet
				chainID("provi"): ChainState{
					ClientsFrozenHeights: &map[string]clienttypes.Height{
						"07-tendermint-0": {
							RevisionNumber: 0,
							RevisionHeight: 0,
						},
					},
				},
			},
		},
		{
			action: updateLightClientAction{
				hostChain:     chainID("provi"),
				relayerConfig: forkRelayerConfig,
				clientID:      consumerClientID,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 0,
						validatorID("bob"):   20,
					},
					ClientsFrozenHeights: &map[string]clienttypes.Height{
						"07-tendermint-0": {
							RevisionNumber: 0,
							RevisionHeight: 1,
						},
					},
				},
				chainID(consumerName): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 511,
						validatorID("bob"):   20,
					},
				},
			},
		},
	}
}
