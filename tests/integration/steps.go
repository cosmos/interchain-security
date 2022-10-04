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
	stepsStartChains("consu", "", false),
	stepsDelegate("consu"),
	stepsUnbondRedelegate("consu"),
	stepsDowntime("consu"),
)

var democracySteps = concatSteps(
	// democracySteps requires a transfer channel and overrides genesis
	stepsStartChains("democ", ".app_state.ccvconsumer.params.blocks_per_distribution_transmission = \"10\"", true),
	stepsDelegate("democ"),
	stepsDemocracy("democ"),
)
