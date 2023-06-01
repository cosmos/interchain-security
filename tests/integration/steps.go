package main

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

func generateSimpleTestSteps() []Step {
	startChainStep := []Step{
		{
			action: StartChainAction{
				chain: chainID("provi"),
				validators: []StartChainValidator{
					{id: validatorID("bob"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("alice"), stake: 500000000, allocation: 10000000000},
					{id: validatorID("carol"), stake: 500000000, allocation: 10000000000},
				},
			},
			state: State{
				chainID("provi"): ChainState{
					ValBalances: &map[validatorID]uint{
						validatorID("alice"): 9500000000,
						validatorID("bob"):   9500000000,
						validatorID("carol"): 9500000000,
					},
				},
			},
		},
	}

	sendTokenSteps := []Step{}
	for i := 1; i < 100; i++ {
		diff := uint(i * 100)
		sendTokenSteps = append(sendTokenSteps,
			Step{
				action: SendTokensAction{
					chain:  chainID("provi"),
					from:   validatorID("alice"),
					to:     validatorID("bob"),
					amount: 100,
				},
				state: State{
					chainID("provi"): ChainState{
						ValBalances: &map[validatorID]uint{
							validatorID("alice"): 9500000000 - diff,
							validatorID("bob"):   9500000000 + diff,
						},
					},
				},
			})
	}

	return concatSteps(startChainStep, sendTokenSteps)
}

var simpleTestSteps = generateSimpleTestSteps()

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
	stepsStartRelayer(),
	stepsConsumerRemovalPropNotPassing("consu", 3), // submit removal prop but vote no on it - chain should stay
	stepsStopChain("consu", 4),                     // stop chain
)

var cometMockHappyPath = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsUnbond("consu"),
	stepsRedelegate("consu"),
	stepsStartRelayer(),
	stepsConsumerRemovalPropNotPassing("consu", 2), // submit removal prop but vote no on it - chain should stay
	stepsStopChain("consu", 3),                     // stop chain
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
