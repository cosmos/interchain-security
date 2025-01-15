package main

import (
	gov "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
)

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

// Reduced set of basic test steps suited for compatibility testing
var compatibilitySteps = concatSteps(
	compstepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsUnbond("consu"),
	stepsRedelegate("consu"),
	stepsDowntime("consu"),
	stepsDoubleSignOnProvider("consu"), // carol double signs on provider
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
	stepsRedelegate("consu"),
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
	stepsRedelegate("consu"),
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

// these tests start with transfer SendEnabled set to false
// one of the steps will set SendEnabled to true
var democracyUnregisteredDenomSteps = concatSteps(
	// democracySteps requires a transfer channel
	stepsStartChains([]string{"democ"}, true),
	// delegation needs to happen so the first VSC packet can be delivered
	stepsDelegate("democ"),
	// the denom is not registered on the provider chain so it will not be distributed as rewards
	stepsDemocracy("democ", false),
)

// these tests start with transfer SendEnabled set to true
var democracyRegisteredDenomSteps = concatSteps(
	// democracySteps requires a transfer channel
	stepsStartChains([]string{"democ"}, true),
	// delegation needs to happen so the first VSC packet can be delivered
	stepsDelegate("democ"),
	// the denom is registered on the provider chain so it will be distributed as rewards
	stepsDemocracy("democ", true),
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

var consumerMisbehaviourSteps = concatSteps(
	// start provider and consumer chain
	stepsStartChainsForConsumerMisbehaviour("consu"),
	// make a consumer validator to misbehave and get jailed
	stepsCauseConsumerMisbehaviour("consu"),
)

var consumerDoubleSignSteps = concatSteps(
	// start provider and consumer chain
	stepsStartChains([]string{"consu"}, false),
	// make a consumer validator double sign and get jailed
	stepsCauseDoubleSignOnConsumer("consu", "provi"),
)

var consumerDoubleDowntimeSteps = concatSteps(
	stepsStartChains([]string{"consu"}, false),
	stepsDelegate("consu"),
	stepsUnbond("consu"),
	stepsRedelegate("consu"),
	stepsDoubleDowntime("consu"),
)

func stepsInactiveValsTopNReproduce() []Step {
	alice_power := uint(30)
	bob_power := uint(29)
	carol_power := uint(20)
	david_power := uint(10)
	eve_power := uint(7)
	fred_power := uint(4)

	return []Step{
		{
			Action: StartChainAction{
				Chain: ChainID("provi"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("alice"), Stake: alice_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("bob"), Stake: bob_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("carol"), Stake: carol_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("david"), Stake: david_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("eve"), Stake: eve_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("fred"), Stake: fred_power * 1000000, Allocation: 10000000000},
				},
			},
			State: State{
				ChainID("provi"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): alice_power,
						ValidatorID("bob"):   bob_power,
						ValidatorID("carol"): carol_power,
						ValidatorID("david"): david_power,
						ValidatorID("eve"):   0, // max provider consensus validators is 4, so eve and fred are at 0 power
						ValidatorID("fred"):  0,
					},
					StakedTokens: &map[ValidatorID]uint{
						ValidatorID("alice"): alice_power * 1000000,
						ValidatorID("bob"):   bob_power * 1000000,
						ValidatorID("carol"): carol_power * 1000000,
						ValidatorID("david"): david_power * 1000000,
						ValidatorID("eve"):   eve_power * 1000000,
						ValidatorID("fred"):  fred_power * 1000000,
					},
				},
			},
		},
		{
			Action: SubmitConsumerAdditionProposalAction{
				Chain:             ChainID("provi"),
				From:              ValidatorID("alice"),
				Deposit:           10000001,
				ConsumerChain:     ChainID("consu"),
				SpawnTime:         0,
				InitialHeight:     clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
				TopN:              100,
				AllowInactiveVals: false,
			},
			State: State{
				ChainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         ChainID("consu"),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        gov.ProposalStatus_PROPOSAL_STATUS_VOTING_PERIOD.String(),
						},
					},
				},
			},
		},
		{
			Action: VoteGovProposalAction{
				Chain:      ChainID("provi"),
				From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol"), ValidatorID("david"), ValidatorID("eve")},
				Vote:       []string{"yes", "yes", "yes", "yes", "yes"},
				PropNumber: 1,
			},
			State: State{
				ChainID("provi"): ChainState{
					Proposals: &map[uint]Proposal{
						1: ConsumerAdditionProposal{
							Deposit:       10000001,
							Chain:         ChainID("consu"),
							SpawnTime:     0,
							InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
							Status:        gov.ProposalStatus_PROPOSAL_STATUS_PASSED.String(),
						},
					},
					HasToValidate: &map[ValidatorID][]ChainID{
						ValidatorID("alice"): {"consu"},
						ValidatorID("bob"):   {"consu"},
						ValidatorID("carol"): {"consu"},
						ValidatorID("david"): {"consu"},
						ValidatorID("eve"):   {},
						ValidatorID("fred"):  {},
					},
				},
			},
		},
		{
			Action: StartConsumerChainAction{
				ConsumerChain: ChainID("consu"),
				ProviderChain: ChainID("provi"),
				Validators: []StartChainValidator{
					{Id: ValidatorID("alice"), Stake: alice_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("bob"), Stake: bob_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("carol"), Stake: carol_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("david"), Stake: david_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("eve"), Stake: eve_power * 1000000, Allocation: 10000000000},
					{Id: ValidatorID("fred"), Stake: fred_power * 1000000, Allocation: 10000000000},
				},
				// For consumers that're launching with the provider being on an earlier version
				// of ICS before the soft opt-out threshold was introduced, we need to set the
				// soft opt-out threshold to 0.05 in the consumer genesis to ensure that the
				// consumer binary doesn't panic. Sdk requires that all params are set to valid
				// values from the genesis file.
				GenesisChanges: ".app_state.ccvconsumer.params.soft_opt_out_threshold = \"0.05\"",
			},
			State: State{
				ChainID("consu"): ChainState{
					ValPowers: &map[ValidatorID]uint{
						ValidatorID("alice"): alice_power,
						ValidatorID("bob"):   bob_power,
						ValidatorID("carol"): carol_power,
						ValidatorID("david"): david_power,
						ValidatorID("eve"):   0,
						ValidatorID("fred"):  0,
					},
				},
			},
		},
	}
}
