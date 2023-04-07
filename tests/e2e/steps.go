package main

import clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"

type Step struct {
	action interface{}
	state  State
}

func concatSteps(steps ...[]Step) []Step {
	var concat []Step
	for _, s := range steps {
		concat = append(concat, s...)
	}
	return concat
}

var happyPathSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsAssignConsumerKeyOnStartedChain("consu", "bob"),
	stepsUnbond("consu"),
	stepsRedelegate("consu"),
	stepsDowntime("consu"),
	stepsRejectEquivocationProposal("consu", 2),   // prop to tombstone bob is rejected
	stepsDoubleSignOnProviderAndConsumer("consu"), // carol double signs on provider, bob double signs on consumer
	stepsSubmitEquivocationProposal("consu", 2),   // now prop to tombstone bob is submitted and accepted
	stepsStartHermes(),
	stepsConsumerRemovalPropNotPassing("consu", 3), // submit removal prop but vote no on it - chain should stay
	stepsStopChain("consu", 4),                     // stop chain
)

var slashThrottleSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsThrottledDowntime("consu"),
	stepsStopChain("consu", 2),
)

var democracySteps = concatSteps(
	// democracySteps requires a transfer channel
	stepsStartChains([]string{"democ"}, true),
	// delegation needs to happen so the first VSC packet can be delivered
	stepsDelegate("democ"),
	stepsDemocracy("democ"),
)

var multipleConsumers = concatSteps(
	stepsStartChains([]string{"consu", "densu"}, false),
	stepsMultiConsumerDelegate("consu", "densu"),
	stepsMultiConsumerUnbond("consu", "densu"),
	stepsMultiConsumerRedelegate("consu", "densu"),
	stepsMultiConsumerDowntimeFromConsumer("consu", "densu"),
	stepsMultiConsumerDowntimeFromProvider("consu", "densu"),
	stepsMultiConsumerDoubleSign("consu", "densu"), // double sign on one of the chains
)

var softOptOutSteps = concatSteps(
	[]Step{
		{
			action: StartChainAction{
				chain: chainID("provi"),
				validators: []StartChainValidator{
					{id: validatorID("bob"), stake: 10000000, allocation: 10000000000},
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("carol"), stake: 500000000, allocation: 10000000000},
				},
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9900000000,
						validatorID("bob"):   9500000000,
						validatorID("carol"): 9500000000,
					},
				},
			},
		},
		{
			action: submitConsumerAdditionProposalAction{
				chain:         chainID("provi"),
				from:          validatorID("alice"),
				deposit:       10000001,
				consumerChain: chainID("consu"),
				spawnTime:     0,
				initialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
			},
			state: State{
				chainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         chainID("consu"),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_VOTING_PERIOD",
						},
					},
				},
			},
		},
		{
			action: voteGovProposalAction{
				chain:      chainID("provi"),
				from:       []validatorID{validatorID("alice"), validatorID("bob"), validatorID("carol")},
				vote:       []string{"yes", "yes", "yes"},
				propNumber: 1,
			},
			state: State{
				chainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         chainID("consu"),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        "PROPOSAL_STATUS_PASSED",
						},
					},
				},
			},
		},
		{
			action: startConsumerChainAction{
				consumerChain: chainID("consu"),
				providerChain: chainID("provi"),
				validators: []StartChainValidator{
					{id: validatorID("bob"), stake: 10000000, allocation: 10000000000},
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("carol"), stake: 500000000, allocation: 10000000000},
				},
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9900000000,
						validatorID("bob"):   9500000000,
						validatorID("carol"): 9500000000,
					},
				},
				chainID("consu"): ChainState{
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
				chainA:  chainID("consu"),
				chainB:  chainID("provi"),
				clientA: 0,
				clientB: 1,
			},
			state: State{},
		},
		{
			action: addIbcChannelAction{
				chainA:      chainID("consu"),
				chainB:      chainID("provi"),
				connectionA: 0,
				portA:       "consumer", // TODO: check port mapping
				portB:       "provider",
				order:       "ordered",
			},
			state: State{},
		},
		{
			action: downtimeSlashAction{
				chain:     chainID("consu"),
				validator: validatorID("alice"),
			},
			state: State{
				// validator should be slashed on consumer, powers not affected on either chain yet
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
				chainID("consu"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
		{
			action: relayPacketsAction{
				chain:   chainID("provi"),
				port:    "provider",
				channel: 0,
			},
			state: State{
				chainID("provi"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 10,
						// Downtime jailing and corresponding voting power change is not processed by provider
						// because alice is smaller than the threshold
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
				chainID("consu"): ChainState{
					ValPowers: &map[validatorID]uint{
						validatorID("alice"): 509,
						validatorID("bob"):   500,
						validatorID("carol"): 501,
					},
				},
			},
		},
	},
)
