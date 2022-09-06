package core

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

const P = "provider"
const C = "consumer"

// ValStates represents the total delegation
// and bond status of a validator
type ValStates struct {
	Delegation           []int
	Tokens               []int
	ValidatorExtraTokens []int
	Status               []stakingtypes.BondStatus
}

type InitState struct {
	PKSeeds                []string
	NumValidators          int
	MaxValidators          int
	InitialDelegatorTokens int
	SlashDoublesign        sdk.Dec
	SlashDowntime          sdk.Dec
	UnbondingP             time.Duration
	UnbondingC             time.Duration
	Trusting               time.Duration
	MaxClockDrift          time.Duration
	BlockSeconds           time.Duration
	ConsensusParams        *abci.ConsensusParams
	ValStates              ValStates
	MaxEntries             int
}

var initState InitState

func init() {
	//	tokens === power
	sdk.DefaultPowerReduction = sdk.NewInt(1)
	initState = InitState{
		PKSeeds: []string{
			// Fixed seeds are used to create the private keys for validators.
			// The seeds are chosen to ensure that the resulting validators are
			// sorted in descending order by the staking module.
			"bbaaaababaabbaabababbaabbbbbbaaa",
			"abbbababbbabaaaaabaaabbbbababaab",
			"bbabaabaabbbbbabbbaababbbbabbbbb",
			"aabbbabaaaaababbbabaabaabbbbbbba"},
		NumValidators:          4,
		MaxValidators:          2,
		InitialDelegatorTokens: 10000000000000,
		SlashDoublesign:        sdk.NewDec(0),
		SlashDowntime:          sdk.NewDec(0),
		UnbondingP:             time.Second * 70,
		UnbondingC:             time.Second * 50,
		Trusting:               time.Second * 49,
		MaxClockDrift:          time.Second * 10000,
		BlockSeconds:           time.Second * 6,
		ValStates: ValStates{
			Delegation:           []int{4000, 3000, 2000, 1000},
			Tokens:               []int{5000, 4000, 3000, 2000},
			ValidatorExtraTokens: []int{1000, 1000, 1000, 1000},
			Status: []stakingtypes.BondStatus{stakingtypes.Bonded, stakingtypes.Bonded,
				stakingtypes.Unbonded, stakingtypes.Unbonded},
		},
		MaxEntries: 1000000,
		ConsensusParams: &abci.ConsensusParams{
			Block: &abci.BlockParams{
				MaxBytes: 9223372036854775807,
				MaxGas:   9223372036854775807,
			},
			Evidence: &tmproto.EvidenceParams{
				MaxAgeNumBlocks: 302400,
				MaxAgeDuration:  504 * time.Hour, // 3 weeks is the max duration
				MaxBytes:        10000,
			},
			Validator: &tmproto.ValidatorParams{
				PubKeyTypes: []string{
					tmtypes.ABCIPubKeyTypeEd25519,
				},
			},
		},
	}
}
