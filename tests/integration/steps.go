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
)

var democracySteps = concatSteps(
	// democracySteps requires a transfer channel
	stepsStartChains([]string{"democ"}, true),
	stepsDelegate("democ"),
	stepsDemocracy("democ"),
)

func withSovereignChain(tr *TestRun, consumerNames []string) []Step {
	return concatSteps(
		stepsStartChains(consumerNames, false),
		startSovereignChain(tr, append([]string{"provi"}, consumerNames...)),
		stepsIBCSend(),
	)
}
