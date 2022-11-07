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
	stepsStartChains("consu", false),
	stepsDelegate("consu"),
	stepsUnbondRedelegate("consu"),
	stepsDowntime("consu"),
	stepsStopChain("consu"),
)

var democracySteps = concatSteps(
	// democracySteps requires a transfer channel
	stepsStartChains("democ", true),
	stepsDelegate("democ"),
	stepsDemocracy("democ"),
)

var doubleSignProviderSteps = concatSteps(
	stepsStartChains("consu", false),
	stepsDoubleSign("consu", "provi", "carol"),
)
