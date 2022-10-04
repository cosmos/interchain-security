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
	stepsStartChains("consu"),
	stepsDelegation("consu"),
	stepsDowntime("consu"),
)

// var democracySteps = concatSteps(
// 	stepsStartChains("democ"),
// 	stepsDemocracy("democ"),
// )
