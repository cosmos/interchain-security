package main

import (
	"time"

	gov "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	clienttypes "github.com/cosmos/ibc-go/v9/modules/core/02-client/types"
	e2e "github.com/cosmos/interchain-security/v7/tests/e2e/testlib"
)

// stepsPermissionlessICS tests
// - starting multiple permissionless consumer chains with the same chain ID
// - that a validator CAN opt-in on two different chains with the same chain ID
// - taking ownership of a consumer chain
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
				State: State{
					ChainID("provi"): e2e.ChainState{
						ConsumerChains: &map[ChainID]bool{"cons2": true},
					},
				},
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
		// Start another permissionless chain by 'alice'
		// - runs chain "cons1" which is configured with ChainID "consu"
		// - test that validator 'alice' can opt-in on two chain with same chain ID
		stepsStartPermissionlessChain(
			"cons1", "consu",
			[]string{"cons1", "cons2"}, // show up both consumer chains as proposed chains
			[]ValidatorID{
				ValidatorID("bob"),
				ValidatorID("alice")}, // alice already validating 'cons2'
			0),

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
						ConsumerChains: &map[ChainID]bool{"cons2": true, "cons1": true},
						HasToValidate: &map[ValidatorID][]ChainID{
							ValidatorID("alice"): {"cons1"}, // cons2 is not part of it as it did not start
							ValidatorID("bob"):   {"cons1"},
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
					NewOwner:      getDefaultValidators()[ValidatorID("carol")].ValoperAddress,
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
							ValidatorID("alice"): {"cons1"},
							ValidatorID("bob"):   {"cons1"}, // bob is still a validator on cons1 chain
							ValidatorID("carol"): {},
						},
					},
				},
			},
		},
		// Remove permissionless chain
		[]Step{
			{
				Action: RemoveConsumerChainAction{
					Chain:         ChainID("provi"),
					From:          ValidatorID("alice"),
					ConsumerChain: ChainID("cons1"),
				},
				State: State{
					ChainID("provi"): e2e.ChainState{
						ConsumerChains: &map[ChainID]bool{"cons2": true}, // Consumer chain "cons1" is now removed
						HasToValidate: &map[ValidatorID][]ChainID{
							ValidatorID("alice"): {},
							ValidatorID("bob"):   {},
							ValidatorID("carol"): {},
						},
					},
				},
			},
		},
	)
	return s
}

// stepsPermissionlessTopN tests transformation of TopN chains to permissionless
func stepsPermissionlessTopN() []Step {
	s := concatSteps(
		// Start provider and a TopN consumer chain
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
			// Propose a TopN chain
			{
				Action: SubmitConsumerAdditionProposalAction{
					Chain:         ChainID("provi"),
					From:          ValidatorID("alice"),
					Deposit:       10000001,
					ConsumerChain: ChainID("cons1"),
					SpawnTime:     0,
					InitialHeight: clienttypes.Height{RevisionNumber: 0, RevisionHeight: 1},
					TopN:          100,
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
				// change the consumer key "carol" is using on the consumer chain to be the one "carol" uses when opting in
				Action: AssignConsumerPubKeyAction{
					Chain:           ChainID("cons1"),
					Validator:       ValidatorID("carol"),
					ConsumerPubkey:  getDefaultValidators()[ValidatorID("carol")].ConsumerValPubKey,
					ReconfigureNode: true,
				},
				State: State{},
			},

			// Vote on the proposal
			{
				Action: VoteGovProposalAction{
					Chain:      ChainID("provi"),
					From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob")},
					Vote:       []string{"yes", "yes"},
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
					},
				},
			},
			// Start the chain
			{
				Action: StartConsumerChainAction{
					ConsumerChain: ChainID("cons1"),
					ProviderChain: ChainID("provi"),
					Validators: []StartChainValidator{
						{Id: ValidatorID("alice"), Stake: 100000000, Allocation: 10000000000},
						{Id: ValidatorID("bob"), Stake: 200000000, Allocation: 10000000000},
						{Id: ValidatorID("carol"), Stake: 300000000, Allocation: 10000000000},
					},
				},
				State: State{
					ChainID("cons1"): ChainState{
						ValPowers: &map[ValidatorID]uint{
							ValidatorID("alice"): 100,
							ValidatorID("bob"):   200,
							ValidatorID("carol"): 300,
						},
					},
				},
			},
			{
				Action: AddIbcConnectionAction{
					ChainA:  ChainID("cons1"),
					ChainB:  ChainID("provi"),
					ClientA: 0,
					ClientB: 0,
				},
				State: State{},
			},
			{
				Action: AddIbcChannelAction{
					ChainA:      ChainID("cons1"),
					ChainB:      ChainID("provi"),
					ConnectionA: 0,
					PortA:       "consumer",
					PortB:       "provider",
					Order:       "ordered",
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
							ValidatorID("bob"):   200,
							ValidatorID("carol"): 300,
						},
					},
					ChainID("provi"): ChainState{
						HasToValidate: &map[ValidatorID][]ChainID{
							ValidatorID("alice"): {"cons1"},
							ValidatorID("bob"):   {"cons1"},
							ValidatorID("carol"): {"cons1"},
						},
					},
				},
			},
		},
		// Convert TopN chain "cons1" to a permissionless chain owned by "carol" submitted by "alice"
		[]Step{
			{
				Action: SubmitConsumerModificationProposalAction{
					Chain:         ChainID("provi"),
					From:          ValidatorID("alice"),
					Deposit:       10000001,
					ConsumerChain: ChainID("cons1"),
					NewOwner:      getDefaultValidators()[ValidatorID("carol")].DelAddress,
					TopN:          0,
				},
				State: State{
					ChainID("provi"): ChainState{
						Proposals: &map[uint]Proposal{
							2: ConsumerAdditionProposal{
								Deposit: 10000001,
								Chain:   ChainID("consu"),
								Status:  gov.ProposalStatus_PROPOSAL_STATUS_VOTING_PERIOD.String(),
							},
						},
					},
				},
			},
			{
				Action: VoteGovProposalAction{
					Chain:      ChainID("provi"),
					From:       []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol")},
					Vote:       []string{"yes", "yes", "yes"},
					PropNumber: 2,
				},
				State: State{
					ChainID("provi"): ChainState{
						Proposals: &map[uint]Proposal{
							2: ConsumerAdditionProposal{
								Deposit: 10000001,
								Chain:   ChainID("consu"),
								Status:  gov.ProposalStatus_PROPOSAL_STATUS_PASSED.String(),
							},
						},
					},
				},
			},
			// Check ownership by denylisting "alice" from the transformed consumer chain by new owner "carol"
			{
				Action: UpdateConsumerChainAction{
					Chain:         ChainID("provi"),
					From:          ValidatorID("carol"),
					ConsumerChain: ChainID("cons1"),
					InitParams:    nil,
					PowerShapingParams: &PowerShapingParameters{
						TopN:     0,
						Denylist: []string{getDefaultValidators()[ValidatorID("alice")].ValconsAddress},
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
							ValidatorID("alice"): 0, // alice got denylisted
							ValidatorID("bob"):   200,
							ValidatorID("carol"): 300,
						},
					},
					ChainID("provi"): e2e.ChainState{
						HasToValidate: &map[ValidatorID][]ChainID{
							ValidatorID("alice"): {}, // alice is denylisted on "cons1"
							ValidatorID("bob"):   {"cons1"},
							ValidatorID("carol"): {"cons1"},
						},
					},
				},
			},
		},
	)
	return s
}
