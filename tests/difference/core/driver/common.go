package core

import (
	"time"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmproto "github.com/cometbft/cometbft/proto/tendermint/types"
	tmtypes "github.com/cometbft/cometbft/types"
)

const (
	P = "provider"
	C = "consumer"
)

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
	SlashDoublesign        math.LegacyDec
	SlashDowntime          math.LegacyDec
	UnbondingP             time.Duration
	UnbondingC             time.Duration
	Trusting               time.Duration
	MaxClockDrift          time.Duration
	BlockInterval          time.Duration
	ConsensusParams        *tmproto.ConsensusParams
	ValStates              ValStates
	MaxEntries             int
}

var initStateVar InitState

func init() {
	//	tokens === power
	sdk.DefaultPowerReduction = math.NewInt(1)
	initStateVar = InitState{
		PKSeeds: []string{
			// Fixed seeds are used to create the private keys for validators.
			// The seeds are chosen to ensure that the resulting validators are
			// sorted in descending order by the staking module.
			"bbaaaababaabbaabababbaabbbbbbaaa",
			"abbbababbbabaaaaabaaabbbbababaab",
			"bbabaabaabbbbbabbbaababbbbabbbbb",
			"aabbbabaaaaababbbabaabaabbbbbbba",
		},
		NumValidators:          4,
		MaxValidators:          2,
		InitialDelegatorTokens: 10000000000000,
		SlashDoublesign:        math.LegacyNewDec(0),
		SlashDowntime:          math.LegacyNewDec(0),
		UnbondingP:             time.Second * 70,
		UnbondingC:             time.Second * 50,
		Trusting:               time.Second * 49,
		MaxClockDrift:          time.Second * 10000,
		BlockInterval:          time.Second * 6,
		ValStates: ValStates{
			Delegation:           []int{4000, 3000, 2000, 1000},
			Tokens:               []int{5000, 4000, 3000, 2000},
			ValidatorExtraTokens: []int{1000, 1000, 1000, 1000},
			Status: []stakingtypes.BondStatus{
				stakingtypes.Bonded, stakingtypes.Bonded,
				stakingtypes.Unbonded, stakingtypes.Unbonded,
			},
		},
		MaxEntries: 1000000,
		ConsensusParams: &tmproto.ConsensusParams{
			Block: &tmproto.BlockParams{
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
