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

var happyPathSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsAssignConsumerKeyOnStartedChain("consu", "bob"),
	stepsUnbond("consu"),
	stepsRedelegateForOptOut("consu"),
	stepsDowntimeWithOptOut("consu"),
	stepsRedelegate("consu"),
	stepsDowntime("consu"),
	stepsRejectEquivocationProposal("consu", 2),   // prop to tombstone bob is rejected
	stepsDoubleSignOnProviderAndConsumer("consu"), // carol double signs on provider, bob double signs on consumer
	stepsSubmitEquivocationProposal("consu", 2),   // now prop to tombstone bob is submitted and accepted
	stepsStartRelayer(),
	stepsConsumerRemovalPropNotPassing("consu", 3), // submit removal prop but vote no on it - chain should stay
	stepsStopChain("consu", 4),                     // stop chain
)

var shortHappyPathSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsUnbond("consu"),
	stepsRedelegateShort("consu"),
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

var rewardDenomConsumerSteps = concatSteps(
	// democracySteps requires a transfer channel
	stepsStartChains([]string{"democ"}, true),
	// delegation needs to happen so the first VSC packet can be delivered
	stepsDelegate("democ"),
	stepsRewardDenomConsumer("democ"),
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

var changeoverSteps = concatSteps(
	// stepStartProviderChain(),
	// start chain and test delegation operation
	stepRunSovereignChain(),

	// setup upgrade proposal on sovereign so it halts
	// setup consumer launch proposal on provider
	// copy over the sovereign state to the consumer
	// start consumer
	// run happy path
)
