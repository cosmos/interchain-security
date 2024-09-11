package main

import (
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	e2e "github.com/cosmos/interchain-security/v6/tests/e2e/testlib"
)

// stepsPermissionlessICS tests
// - starting multiple permissionless consumer chains with the same chain ID
// - that a validator CAN opt-in on two different chains with the same chain ID
// - taking ownership of a consumer chain
// - TopN to permissionless chain transformation
func stepsPermissionlessICS() []Step {
	s := concatSteps(
		[]Step{
			// Start the provider chain
			{
				Action: StartChainAction{
					Chain: ChainID("provi"),
					Validators: []StartChainValidator{
						{Id: ValidatorID("alice"), Stake: 100000000, Allocation: 10000000000},
						{Id: ValidatorID("bob"), Stake: 200000000, Allocation: 10000000000},
						{Id: ValidatorID("carol"), Stake: 300000000, Allocation: 10000000000},
					},
				},
				State: State{
					ChainID("provi"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100,
							ValidatorID("bob"):   200,
							ValidatorID("carol"): 300,
						},
					},
				},
			},

			// Initialize a permissionless chain with ChainID `consu`
			// - create the consumer chain
			// - opt-in a validator
			// - launch the chain
			{
				Action: CreateConsumerChainAction{
					Chain:         ChainID("provi"),
					From:          ValidatorID("alice"),
					ConsumerChain: ChainID("cons2"), // test chain "cons2" is configured with ChainID "consu"
					InitParams: &InitializationParameters{
						InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
						SpawnTime:     uint(time.Minute * 3),
					},
					PowerShapingParams: &PowerShapingParameters{
						TopN: 0,
					},
				},
				State: State{},
			},
			{
				Action: OptInAction{
					Chain:     ChainID("cons2"),
					Validator: ValidatorID("alice"),
				},
				State: State{
					ChainID("provi"): ChainState{
						HasToValidate: &map[ValidatorID][]ChainID{
							ValidatorID("alice"): {},
							ValidatorID("bob"):   {},
							ValidatorID("carol"): {},
						},
					},
				},
			},
		},
		// Start another permissionless chain with ChainID `consu`
		// - runs chain "cons1" which is configured with ChainID "consu"
		// - test that validator 'alice' can opt-in on two chain with same chain ID
		stepsStartPermissionlessChain(
			"cons1", "consu",
			[]string{"consu", "consu"},                                  // show up both consumer chains "consu" as proposed chains
			[]ValidatorID{ValidatorID("bob"), ValidatorID("alice")}, 0), // alice already validating 'cons2'

		[]Step{
			{
				Action: RelayPacketsAction{
					ChainA:  ChainID("provi"),
					ChainB:  ChainID("cons1"),
					Port:    "provider",
					Channel: 0,
				},
				State: State{
					ChainID("cons1"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100,
							ValidatorID("bob"):   200,
							ValidatorID("carol"): 0,
						},
					},
					ChainID("provi"): e2e.ChainState{
						HasToValidate: &map[ValidatorID][]ChainID{
							ValidatorID("alice"): {"consu"},
							ValidatorID("bob"):   {"consu"},
							ValidatorID("carol"): {},
						},
					},
				},
			},
		},
		// test chain hijacking prevention
		[]Step{
			// Try to change owner of chain and change deny-/allowlist
			{
				Action: UpdateConsumerChainAction{
					Chain:         ChainID("provi"),
					From:          ValidatorID("bob"),
					ConsumerChain: ChainID("cons1"),
					NewOwner:      getDefaultValidators()[ValidatorID("carol")].ValconsAddress,
					InitParams: &InitializationParameters{
						InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
						SpawnTime:     0, // launch now
					},
					PowerShapingParams: &PowerShapingParameters{
						TopN: 0,
					},
				},
				State: State{},
			},
			{
				Action: UpdateConsumerChainAction{
					Chain:         ChainID("provi"),
					From:          ValidatorID("carol"),
					ConsumerChain: ChainID("cons1"),
					InitParams: &InitializationParameters{
						InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
						SpawnTime:     0,
					},
					PowerShapingParams: &PowerShapingParameters{
						TopN:      0,
						Allowlist: []string{getDefaultValidators()[ValidatorID("carol")].ValconsAddress},
						Denylist:  []string{getDefaultValidators()[ValidatorID("bob")].ValconsAddress},
					},
				},
				State: State{},
			},
			{
				Action: RelayPacketsAction{
					ChainA:  ChainID("provi"),
					ChainB:  ChainID("cons1"),
					Port:    "provider",
					Channel: 0,
				},
				State: State{
					ChainID("cons1"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100,
							ValidatorID("bob"):   200, // bob is not 'denylisted'
							ValidatorID("carol"): 0,
						},
					},
					ChainID("provi"): e2e.ChainState{
						HasToValidate: &map[ValidatorID][]ChainID{
							ValidatorID("alice"): {"consu"},
							ValidatorID("bob"):   {"consu"}, // bob is still a validator on consu chain
							ValidatorID("carol"): {},
						},
					},
				},
			},
		},
	)
	return s
}
