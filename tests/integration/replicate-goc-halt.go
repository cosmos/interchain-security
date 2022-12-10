package main

import (
	"fmt"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
)

func getValidators99() []StartChainValidator {
	validators := []StartChainValidator{}

	for i := 1; i <= 99; i++ {
		validators = append(validators, StartChainValidator{id: validatorID(i), stake: 500000000, allocation: 10000000000})
	}

	return validators
}

func getValBalances99a() *map[validatorID]uint {
	valBalances := map[validatorID]uint{}

	for i := 1; i <= 99; i++ {
		valBalances[validatorID(i)] = 9500000000
	}

	return &valBalances
}

func getValBalances99b() *map[validatorID]uint {
	valBalances := map[validatorID]uint{}

	for i := 1; i <= 99; i++ {
		valBalances[validatorID(i)] = 10000000000
	}

	return &valBalances
}

// This function returns a list of validator IDs from 1 to 99
func getValidatorIDs99() []validatorID {
	valIds99 := []validatorID{}
	for i := 1; i <= 99; i++ {
		valIds99 = append(valIds99, validatorID(fmt.Sprintf("%d", i)))
	}
	return valIds99
}

// This function returns a list of 99 "yes" votes
func getVotes99() []string {
	votes99 := []string{}
	for i := 1; i <= 99; i++ {
		votes99 = append(votes99, "yes")
	}
	return votes99
}

func stepsStartConsumerChainHalt(consumerName string, proposalIndex, chainIndex uint, setupTransferChans bool) []Step {
	s := []Step{
		{
			action: submitConsumerAdditionProposalAction{
				chain:         chainID("provi"),
				from:          validatorID("1"),
				deposit:       10000001,
				consumerChain: chainID(consumerName),
				spawnTime:     0,
				initialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("1"): 9489999999,
						validatorID("2"): 9500000000,
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
		// {
		// 	action: assignConsumerPubKeyAction{
		// 		chain:     chainID(consumerName),
		// 		validator: validatorID("carol"),
		// 		// consumer chain has not started
		// 		// we don't need to reconfigure the node
		// 		// since it will start with consumer key
		// 		reconfigureNode: false,
		// 	},
		// 	state: State{
		// 		chainID(consumerName): ChainState{
		// 			AssignedKeys: &map[validatorID]string{
		// 				validatorID("carol"): "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
		// 			},
		// 			ProviderKeys: &map[validatorID]string{
		// 				validatorID("carol"): "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
		// 			},
		// 		},
		// 	},
		// },
		{
			action: voteGovProposalAction{
				chain:      chainID("provi"),
				from:       getValidatorIDs99(),
				vote:       getVotes99(),
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
						validatorID("1"): 9500000000,
						validatorID("2"): 9500000000,
					},
				},
			},
		},
		{
			action: startConsumerChainAction{
				consumerChain: chainID(consumerName),
				providerChain: chainID("provi"),
				validators:    getValidators99(),
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: getValBalances99a(),
				},
				chainID(consumerName): ChainState{
					ValBalances: getValBalances99b(),
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

func stepStartProviderChainHalt() []Step {
	validators := []StartChainValidator{}
	valBalances := &map[validatorID]uint{}

	for i := 1; i <= 99; i++ {
		validators = append(validators, StartChainValidator{id: validatorID(i), stake: 500000000, allocation: 10000000000})
		(*valBalances)[validatorID(i)] = 9500000000
	}

	return []Step{
		{
			action: StartChainAction{
				chain:      chainID("provi"),
				validators: validators,
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: valBalances,
				},
			},
		},
	}
}

// starts provider and consumer chains specified in consumerNames
// setupTransferChans will establish a channel for fee transfers between consumer and provider
func stepsStartChainsHalt(consumerNames []string, setupTransferChans bool) []Step {
	s := stepStartProviderChain()
	for i, consumerName := range consumerNames {
		s = append(s, stepsStartConsumerChain(consumerName, uint(i+1), uint(i), setupTransferChans)...)
	}

	return s
}

var haltSteps = concatSteps(
	stepsStartChainsHalt([]string{"consu"}, false),
)
