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
	// stepsAssignConsumerKeyOnStartedChain("consu", "bob"),
	stepsUnbond("consu"),
	stepsCancelUnbond("consu"),
	stepsRedelegateForOptOut("consu"),
	stepsDowntimeWithOptOut("consu"),
	stepsRedelegate("consu"),
	stepsDowntime("consu"),
	stepsDoubleSignOnProviderAndConsumer("consu"), // carol double signs on provider, bob double signs on consumer
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
	stepsDoubleSignOnProviderAndConsumer("consu"), // carol double signs on provider, bob double signs on consumer
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
