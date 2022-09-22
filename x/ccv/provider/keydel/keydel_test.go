package keydel

import (
	"math/rand"
	"testing"

	"github.com/stretchr/testify/require"
)

const TRACE_LEN = 1000
const NUM_VALS = 3
const NUM_FKS = 9

type mapInstruction struct {
	lk LK
	fk FK
}

type TraceState struct {
	MapInstructions []mapInstruction
	LocalUpdates    []update
	TP              int
	TC              int
	TM              int
}

type Driver struct {
	t      *testing.T
	e      *KeyDel
	trace  []TraceState
	lastTP int
	lastTC int
	lastTM int
	// indexed by TP
	mappings       []map[LK]FK
	foreignUpdates [][]update
	localValSets   []ValSet
	// corresponds to TC
	foreignValSet ValSet
}

type ValSet struct {
	keyToPower map[int]int
}

func MakeValSet() ValSet {
	return ValSet{keyToPower: map[int]int{}}
}

func (vs *ValSet) applyUpdates(updates []update) {
	for _, u := range updates {
		delete(vs.keyToPower, u.key)
		if 0 < u.power {
			vs.keyToPower[u.key] = u.power
		}
	}
}

func (d *Driver) applyMapInstructions(instructions []mapInstruction) {
	for _, instruction := range instructions {
		_ = d.e.SetLocalToForeign(instruction.lk, instruction.fk)
	}
	copy := map[LK]FK{}
	for lk, fk := range d.e.localToForeign {
		copy[lk] = fk
	}
	d.mappings = append(d.mappings, copy)
}

func (d *Driver) applyLocalUpdates(localUpdates []update) {
	valSet := MakeValSet()
	for lk, power := range d.localValSets[d.lastTP].keyToPower {
		valSet.keyToPower[lk] = power
	}
	valSet.applyUpdates(localUpdates)
	d.localValSets = append(d.localValSets, valSet)
}

func (d *Driver) runTrace() {

	{
		init := d.trace[0]
		// Set the initial map
		d.applyMapInstructions(init.MapInstructions)
		// Set the initial local set
		d.localValSets = append(d.localValSets, MakeValSet())
		d.localValSets[init.TP].applyUpdates(init.LocalUpdates)
		// Set the initial foreign set
		d.foreignUpdates = append(d.foreignUpdates, d.e.ComputeUpdates(init.TP, init.LocalUpdates))
		d.foreignValSet.applyUpdates(d.foreignUpdates[init.TC])
		d.e.Prune(init.TM)
	}

	require.Len(d.t, d.mappings, 1)
	require.Len(d.t, d.foreignUpdates, 1)
	require.Len(d.t, d.localValSets, 1)

	for _, s := range d.trace[1:] {
		if d.lastTP < s.TP {
			d.applyMapInstructions(s.MapInstructions)
			d.applyLocalUpdates(s.LocalUpdates)
			d.foreignUpdates = append(d.foreignUpdates, d.e.ComputeUpdates(s.TP, s.LocalUpdates))
			d.lastTP = s.TP
		}
		if d.lastTC < s.TC {
			for j := d.lastTC + 1; j <= s.TC; j++ {
				d.foreignValSet.applyUpdates(d.foreignUpdates[j])
			}
			d.lastTC = s.TC
		}
		if d.lastTM < s.TM {
			d.e.Prune(s.TM)
			d.lastTM = s.TM
		}
		d.checkProperties()
		require.True(d.t, d.e.internalInvariants())
	}
}

func (d *Driver) checkProperties() {

	/*
		A consumer who receives vscid i must have a validator set
		equal to the validator set on the provider at vscid id mapped
		through the key delegation.
	*/
	validatorSetReplication := func() {

		// Get the current consumer val set
		foreignSet := d.foreignValSet.keyToPower
		// Get the provider set at the relevant time
		localSet := d.localValSets[d.lastTC].keyToPower

		// Map the consumer set back through the inverse key mapping
		mapping := d.mappings[d.lastTC]
		inverseMapping := map[FK]LK{}
		for lk, fk := range mapping {
			inverseMapping[fk] = lk
		}
		foreignSetAsLocal := map[LK]int{}
		for fk, power := range foreignSet {
			foreignSetAsLocal[inverseMapping[fk]] = power
		}

		// Ensure that the validator sets match exactly
		for lk, expectedPower := range localSet {
			actualPower := foreignSetAsLocal[lk]
			require.Equal(d.t, expectedPower, actualPower)
		}
		for lk, actualPower := range foreignSetAsLocal {
			expectedPower := localSet[lk]
			require.Equal(d.t, expectedPower, actualPower)
		}
	}

	/*
		Two more properties which must be satisfied by KeyDel when
		used correctly inside a wider system:

		TODO: need to rephrase the below because they aren't completely accurate
		the upper bound on time is actually TP (inclusive), not TC.

		1. If a foreign key is delivered to the consumer with positive power at
		   VSCID i then the local key associated to it must be retrievable
		   until i is matured. (Consumer initiated slashing property).
		2. If a foreign key is not delivered to the consumer at any VSCID j
		   with i < j and i is matured, then the foreign key is deleted
		   from storage. (Garbage collection property).
	*/
	queriesAndGarbageCollection := func() {
		expectQueryable := map[FK]bool{}
		// If the foreign key was used in [TimeMaturity + 1, TimeConsumer]
		// it must be queryable.
		for i := d.lastTM + 1; i <= d.lastTP; i++ {
			for _, u := range d.foreignUpdates[i] {
				expectQueryable[u.key] = true
			}
		}
		for fk := 0; fk < NUM_FKS; fk++ {
			_, expect := expectQueryable[fk]

			// Check foreign to local lookup is available (or not)
			_, actual := d.e.usedForeignToLocal[fk]
			require.Equal(d.t, expect, actual)

			// Check internals are consistent
			_, actual = d.e.usedForeignToLastVSCID[fk]
			require.Equal(d.t, expect, actual)
		}
	}

	validatorSetReplication()
	queriesAndGarbageCollection()

}

func getTrace(t *testing.T) []TraceState {

	mappings := func() []mapInstruction {
		ret := []mapInstruction{}
		// Go several times to have overlapping validator updates
		for i := 0; i < 2; i++ {
			// include 0 to all validators
			include := rand.Intn(NUM_VALS + 1)
			for _, lk := range rand.Perm(NUM_VALS)[0:include] {
				ret = append(ret, mapInstruction{lk, rand.Intn(NUM_FKS)})
			}
		}
		return ret
	}

	localUpdates := func() []update {
		ret := []update{}
		// include 0 to all validators
		include := rand.Intn(NUM_VALS + 1)
		for _, lk := range rand.Perm(NUM_VALS)[0:include] {
			ret = append(ret, update{key: lk, power: rand.Intn(3)})
		}
		return ret
	}

	ret := []TraceState{
		{
			// Hard code initial mapping
			MapInstructions: []mapInstruction{{0, 0}, {1, 1}, {2, 2}},
			LocalUpdates:    localUpdates(),
			TP:              0,
			TC:              0,
			TM:              0,
		},
	}

	for i := 0; i < TRACE_LEN; i++ {
		choice := rand.Intn(3)
		last := ret[len(ret)-1]
		if choice == 0 {
			ret = append(ret, TraceState{
				MapInstructions: mappings(),
				LocalUpdates:    localUpdates(),
				TP:              last.TP + 1,
				TC:              last.TC,
				TM:              last.TM,
			})
		}
		if choice == 1 {
			curr := last.TC
			limInclusive := last.TP
			if curr < limInclusive {
				// add in [1, limInclusive - curr]
				// rand in [0, limInclusive - curr - 1]
				// bound is [0, limInclusive - curr)
				newTC := rand.Intn(limInclusive-curr) + curr + 1
				require.True(t, curr < newTC && curr <= limInclusive)
				ret = append(ret, TraceState{
					MapInstructions: nil,
					LocalUpdates:    nil,
					TP:              last.TP,
					TC:              newTC,
					TM:              last.TM,
				})
			}
		}
		if choice == 2 {
			curr := last.TM
			limInclusive := last.TC
			if curr < limInclusive {
				newTM := rand.Intn(limInclusive-curr) + curr + 1
				require.True(t, curr < newTM && curr <= limInclusive)
				ret = append(ret, TraceState{
					MapInstructions: nil,
					LocalUpdates:    nil,
					TP:              last.TP,
					TC:              last.TC,
					TM:              newTM,
				})
			}
		}
	}
	return ret
}

func TestPrototype(t *testing.T) {
	for i := 0; i < 1000; i++ {
		trace := []TraceState{}
		for len(trace) < 2 {
			trace = getTrace(t)
		}
		d := Driver{}
		d.t = t
		e := MakeKeyDel()
		d.e = &e
		d.trace = trace
		d.lastTP = 0
		d.lastTC = 0
		d.lastTM = 0
		d.mappings = []map[LK]FK{}
		d.foreignUpdates = [][]update{}
		d.localValSets = []ValSet{}
		d.foreignValSet = MakeValSet()
		d.runTrace()
	}
}

func TestActual(t *testing.T) {
	/*
		traces := [][]TraceState{}
		for _, trace := range traces {
			d := Driver{}
			d.trace = trace
			d.t = t
			d.runTrace()
		}
	*/
}
