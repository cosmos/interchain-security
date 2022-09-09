package core

import (
	"encoding/json"
	"fmt"
	"io"
	"os"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
)

type Action struct {
	Amt              int    `json:"amt,omitempty"`
	Chain            string `json:"chain,omitempty"`
	InfractionHeight int    `json:"infractionHeight,omitempty"`
	IsDowntime       bool   `json:"isDowntime"`
	Kind             string `json:"kind"`
	NumPackets       int    `json:"numPackets,omitempty"`
	Val              int    `json:"val,omitempty"`
}

type Consequence struct {
	Delegation          []int    `json:"delegation,omitempty"`
	DelegatorTokens     int      `json:"delegatorTokens,omitempty"`
	Jailed              []*int   `json:"jailed,omitempty"`
	OutstandingDowntime []bool   `json:"outstandingDowntime,omitempty"`
	ConsumerPower       []*int   `json:"consumerPower,omitempty"`
	Status              []string `json:"status,omitempty"`
	Tokens              []int    `json:"tokens,omitempty"`
	H                   int      `json:"h,omitempty"`
	T                   int      `json:"t,omitempty"`
}

type ActionAndConsequence struct {
	Action      Action      `json:"action"`
	Consequence Consequence `json:"consequence"`
	Ix          int         `json:"ix"`
}

type TraceData struct {
	Actions   []ActionAndConsequence `json:"actions"`
	Constants struct {
		BlockSeconds            int     `json:"BLOCK_SECONDS"`
		C                       string  `json:"C"`
		DelegateAmtMax          int     `json:"DELEGATE_AMT_MAX"`
		DelegateAmtMin          int     `json:"DELEGATE_AMT_MIN"`
		InitialDelegatorTokens  int     `json:"INITIAL_DELEGATOR_TOKENS"`
		IsdowntimeProbability   float64 `json:"ISDOWNTIME_PROBABILITY"`
		JailSeconds             int     `json:"JAIL_SECONDS"`
		MaxNumPacketsForDeliver int     `json:"MAX_NUM_PACKETS_FOR_DELIVER"`
		MaxValidators           int     `json:"MAX_VALIDATORS"`
		NumValidators           int     `json:"NUM_VALIDATORS"`
		P                       string  `json:"P"`
		SlashDoublesign         int     `json:"SLASH_DOUBLESIGN"`
		SlashDowntime           int     `json:"SLASH_DOWNTIME"`
		TrustingSeconds         int     `json:"TRUSTING_SECONDS"`
		UnbondingSecondsC       int     `json:"UNBONDING_SECONDS_C"`
		UnbondingSecondsP       int     `json:"UNBONDING_SECONDS_P"`
		UndelegateAmtMax        int     `json:"UNDELEGATE_AMT_MAX"`
		UndelegateAmtMin        int     `json:"UNDELEGATE_AMT_MIN"`
	} `json:"constants"`
	Events []string `json:"events"`
	Meta   struct {
		Commit string `json:"commit"`
		Diff   string `json:"diff"`
	} `json:"meta"`
}

func LoadTraces(fn string) []TraceData {

	/* #nosec */
	fd, err := os.Open(fn)

	if err != nil {
		panic(err)
	}

	/* #nosec */
	defer fd.Close()

	byteValue, _ := io.ReadAll(fd)

	var ret []TraceData

	err = json.Unmarshal([]byte(byteValue), &ret)

	if err != nil {
		panic(err)
	}

	return ret
}

// Traces stores a list of traces
// and gives a diagnostic for debugging
// failed tests.
type Traces struct {
	// index of trace in json
	CurrentTraceIx int
	// index of current action
	CurrentActionIx int
	// traces
	Data []TraceData
}

// diagnostic returns a string for diagnosing errors
func (t *Traces) Diagnostic() string {
	return fmt.Sprintf("\n[diagnostic][trace %d, action %d, kind %s]", t.CurrentTraceIx, t.CurrentActionIx, t.Action().Kind)
}

func (t *Traces) Trace() TraceData {
	return t.Data[t.CurrentTraceIx]
}
func (t *Traces) Actions() []ActionAndConsequence {
	return t.Trace().Actions
}

func (t *Traces) Action() Action {
	return t.Data[t.CurrentTraceIx].Actions[t.CurrentActionIx].Action
}

func (t *Traces) Consequence() Consequence {
	return t.Data[t.CurrentTraceIx].Actions[t.CurrentActionIx].Consequence
}

func (t *Traces) Delegation(i int) int {
	return t.Consequence().Delegation[i]
}

func (t *Traces) DelegatorTokens() int {
	return t.Consequence().DelegatorTokens
}

func (t *Traces) Jailed(i int) *int {
	return t.Consequence().Jailed[i]
}

func (t *Traces) OutstandingDowntime(i int) bool {
	return t.Consequence().OutstandingDowntime[i]
}

func (t *Traces) ConsumerPower(i int) *int {
	return t.Consequence().ConsumerPower[i]
}

func (t *Traces) Status(i int) stakingtypes.BondStatus {
	s := t.Consequence().Status[i]
	if s == "unbonding" {
		return stakingtypes.Unbonding
	}
	if s == "unbonded" {
		return stakingtypes.Unbonded
	}
	return stakingtypes.Bonded
}

func (t *Traces) Tokens(i int) int {
	return t.Consequence().Tokens[i]
}

func (t *Traces) Time() int {
	return t.Consequence().T
}

func (t *Traces) Height() int {
	return t.Consequence().H
}
