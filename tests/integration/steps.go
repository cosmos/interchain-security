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
	stepsDelegate([]string{"consu"}),
	stepsUnbond([]string{"consu"}),
	stepsRedelegate([]string{"consu"}),
	stepsDowntime("consu"),
	stepsStopChain("consu"),
)

var democracySteps = concatSteps(
	// democracySteps requires a transfer channel
	stepsStartChains([]string{"democ"}, true),
	// delegation needs to happen so the first VSC packet can be delivered
	stepsDelegate([]string{"democ"}),
	stepsDemocracy("democ"),
)

var doubleSignProviderSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDoubleSign("consu", "provi", "carol"),
)

var multipleConsumers = concatSteps(
	stepsStartChains([]string{"consu", "densu"}, false),
	stepsDelegate([]string{"consu", "densu"}),
	stepsUnbond([]string{"consu", "densu"}),
	stepsRedelegate([]string{"consu", "densu"}),
)
