package main

type Step struct {
	Action interface{}
	State  State
}

func concatSteps(steps ...[]Step) []Step {
	var concat []Step
	for _, s := range steps {
		concat = append(concat, s...)
	}
	return concat
}

// Limited amount of sanity tests to use for compatibility testing
var compatibilitySteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsUnbond("consu"),
	stepsRedelegateShort("consu"),
	stepsDowntime("consu"),
	stepsStartRelayer(),
	stepsConsumerRemovalPropNotPassing("consu", 2), // submit removal prop but vote no on it - chain should stay
	stepsStopChain("consu", 3),                     // stop chain
)

var happyPathSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsAssignConsumerKeyOnStartedChain("consu", "bob"),
	stepsUnbond("consu"),
	stepsCancelUnbond("consu"),
	stepsRedelegateForOptOut("consu"),
	stepsDowntimeWithOptOut("consu"),
	stepsRedelegate("consu"),
	stepsDowntime("consu"),
	stepsDoubleSignOnProvider("consu"), // carol double signs on provider
	stepsStartRelayer(),
	stepsConsumerRemovalPropNotPassing("consu", 2), // submit removal prop but vote no on it - chain should stay
	stepsStopChain("consu", 3),                     // stop chain
)

var shortHappyPathSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsUnbond("consu"),
	stepsRedelegateShort("consu"),
	stepsDowntime("consu"),
	stepsDoubleSignOnProvider("consu"), // carol double signs on provider
	stepsStartRelayer(),
	stepsConsumerRemovalPropNotPassing("consu", 2), // submit removal prop but vote no on it - chain should stay
	stepsStopChain("consu", 3),                     // stop chain
)

var lightClientAttackSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsUnbond("consu"),
	stepsRedelegateShort("consu"),
	stepsDowntime("consu"),
	stepsLightClientAttackOnProviderAndConsumer("consu"), // carol double signs on provider, bob double signs on consumer
	stepsStartRelayer(),
	stepsConsumerRemovalPropNotPassing("consu", 3), // submit removal prop but vote no on it - chain should stay
	stepsStopChain("consu", 4),                     // stop chain
)

var slashThrottleSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsThrottledDowntime("consu"),
	stepsStopChain("consu", 2),
)

var democracyRewardsSteps = concatSteps(
	// democracySteps requires a transfer channel
	stepsStartChains([]string{"democ"}, true),
	// delegation needs to happen so the first VSC packet can be delivered
	stepsDelegate("democ"),
	stepsDemocracy("democ"),
)

var democracySteps = concatSteps(
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
	// start sovereign chain and test delegation operation

	stepRunSovereignChain(),
	stepStartProviderChain(),
	stepsSovereignTransferChan(),

	// the chain will halt once upgrade height is reached
	// after upgrade height is reached, the chain will become a consumer
	stepsUpgradeChain(),
	stepsChangeoverToConsumer("sover"),

	stepsPostChangeoverDelegate("sover"),
)

var consumerMisbehaviourSteps = concatSteps(
	// start provider and consumer chain
	stepsStartChainsWithSoftOptOut("consu"),
	// make a consumer validator to misbehave and get jailed
	stepsCauseConsumerMisbehaviour("consu"),
)

var consumerDoubleSignSteps = concatSteps(
	// start provider and consumer chain
	stepsStartChains([]string{"consu"}, false),
	// make a consumer validator double sign and get jailed
	stepsCauseDoubleSignOnConsumer("consu", "provi"),
)
