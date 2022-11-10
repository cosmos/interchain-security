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
	stepsUnbondRedelegate("consu"),
	stepsDowntime("consu"),
	stepsStopChain("consu"),
)

var democracySteps = concatSteps(
	// democracySteps requires a transfer channel
	stepsStartChains([]string{"democ"}, true),
	// delegation needs to happen so the first VSC packet can be delivered
	stepsDelegate("democ"),
	stepsDemocracy("democ"),
)

var doubleSignProviderSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDoubleSign("consu", "provi", "carol"),
)

var multipleConsumers = concatSteps(
	stepsStartChains([]string{"consu", "densu"}, false),
	stepsMultiConsumerDelegate("consu", "densu"),
	stepsMultiConsumerUnbond("consu", "densu"),
	stepsMultiConsumerRedelegate("consu", "densu"),
	stepsMultiConsumerDowntimeFromConsumer("consu", "densu"),
	stepsMultiConsumerDowntimeFromProvider("consu", "densu"),
)
