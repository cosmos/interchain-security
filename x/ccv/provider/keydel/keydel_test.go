package keydel

import (
	"math/rand"
	"testing"

	"github.com/stretchr/testify/require"
)

const TRACE_LEN = 1000
const NUM_VALS = 3
const NUM_FKS = 9

type TraceState struct {
	Mapping      map[LK]FK
	LocalUpdates []update
	TP           int
	TC           int
	TM           int
}

type Driver struct {
	t      *testing.T
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

func (vs *ValSet) processUpdates(updates []update) {
	for _, u := range updates {
		delete(vs.keyToPower, u.key)
		if 0 < u.power {
			vs.keyToPower[u.key] = u.power
		}
	}
}

func (d *Driver) runTrace() {
	e := MakeKeyDel()

	d.lastTP = 0
	d.lastTC = 0
	d.lastTM = 0
	d.mappings = []map[LK]FK{}
	d.foreignUpdates = [][]update{}
	d.localValSets = []ValSet{}
	d.foreignValSet = MakeValSet()

	init := d.trace[0]
	d.mappings = append(d.mappings, init.Mapping)
	for lk, fk := range init.Mapping {
		e.SetLocalToForeign(lk, fk)
	}
	// Set the initial local set
	d.localValSets = append(d.localValSets, MakeValSet())
	d.localValSets[init.TP].processUpdates(init.LocalUpdates)
	// Set the initial foreign set
	d.foreignUpdates = append(d.foreignUpdates, e.ComputeUpdates(init.TP, init.LocalUpdates))
	d.foreignValSet.processUpdates(d.foreignUpdates[init.TC])
	e.Prune(init.TM)

	require.Len(d.t, d.mappings, 1)
	require.Len(d.t, d.foreignUpdates, 1)
	require.Len(d.t, d.localValSets, 1)

	for _, s := range d.trace[1:] {
		if d.lastTP < s.TP {
			d.mappings = append(d.mappings, s.Mapping)
			d.localValSets = append(d.localValSets, MakeValSet())
			for lk, power := range d.localValSets[d.lastTP].keyToPower {
				d.localValSets[s.TP].keyToPower[lk] = power
			}
			d.localValSets[s.TP].processUpdates(s.LocalUpdates)
			d.lastTP = s.TP
			for lk, fk := range s.Mapping {
				e.SetLocalToForeign(lk, fk)
			}
			d.foreignUpdates = append(d.foreignUpdates, e.ComputeUpdates(s.TP, s.LocalUpdates))
		}
		if d.lastTC < s.TC {
			for j := d.lastTC + 1; j <= s.TC; j++ {
				d.foreignValSet.processUpdates(d.foreignUpdates[j])
			}
			d.lastTC = s.TC
		}
		if d.lastTM < s.TM {
			e.Prune(s.TM)
			d.lastTM = s.TM
		}
		d.checkProperties(e)
		require.True(d.t, e.internalInvariants())
	}
}

func (d *Driver) checkProperties(e KeyDel) {

	/*
		A consumer who receives vscid i must have a validator set
		equal to the validator set on the provider at vscid id mapped
		through the key delegation.
	*/
	validatorSetReplication := func() {
		// Check that the foreign ValSet is equal to the local ValSet
		// at time TC via inverse mapping

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

		1. If a foreign key is delivered to the consumer with positive power at
		   VSCID i then the local key associated to it must be retrievable
		   until i is matured. (Consumer initiated slashing property).
		2. If a foreign key is not delivered to the consumer at any VSCID j
		   with i < j and i is matured, then the foreign key is deleted
		   from storage. (Garbage collection property).
	*/
	queries := func() {
		expectQueryable := map[FK]bool{}
		// If the foreign key was used in [TimeMaturity + 1, TimeConsumer]
		// it must be queryable.
		for i := d.lastTM + 1; i <= d.lastTC; i++ {
			for _, u := range d.foreignUpdates[i] {
				expectQueryable[u.key] = true
			}
		}
		for fk := 0; fk < NUM_FKS; fk++ {
			_, actual := e.usedForeignToLocal[fk]
			_, expect := expectQueryable[fk]
			require.Equal(d.t, expect, actual)
			_, actual = e.usedForeignToLastVSCID[fk]
			require.Equal(d.t, expect, actual)
		}
	}

	validatorSetReplication()
	queries()

}

func getTrace(t *testing.T) []TraceState {

	mapping := func() map[LK]FK {
		// TODO: currently I don't generate partial mappings but I might want to
		// Create a mapping of nums [0, NUM_VALS] mapped injectively to [0, NUM_FKS]
		ret := map[LK]FK{}
		good := func() bool {
			if len(ret) != NUM_VALS {
				return false
			}
			seen := map[FK]bool{}
			for _, fk := range ret {
				if _, ok := seen[fk]; ok {
					return false
				}
				seen[fk] = true
			}
			return true
		}
		for !good() {
			for lk := 0; lk < NUM_VALS; lk++ {
				ret[lk] = rand.Intn(NUM_FKS)
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
			Mapping:      mapping(),
			LocalUpdates: localUpdates(),
			TP:           0,
			TC:           0,
			TM:           0,
		},
	}

	i := 1
	for i < TRACE_LEN {
		choice := rand.Intn(3)
		last := ret[len(ret)-1]
		good := false
		if choice == 0 {
			ret = append(ret, TraceState{
				Mapping:      mapping(),
				LocalUpdates: localUpdates(),
				TP:           last.TP + 1,
				TC:           last.TC,
				TM:           last.TM,
			})
			good = true
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
					Mapping:      nil,
					LocalUpdates: nil,
					TP:           last.TP,
					TC:           newTC,
					TM:           last.TM,
				})
				good = true
			}
		}
		if choice == 2 {
			curr := last.TM
			limInclusive := last.TC
			if curr < limInclusive {
				newTM := rand.Intn(limInclusive-curr) + curr + 1
				require.True(t, curr < newTM && curr <= limInclusive)
				ret = append(ret, TraceState{
					Mapping:      nil,
					LocalUpdates: nil,
					TP:           last.TP,
					TC:           last.TC,
					TM:           newTM,
				})
				good = true
			}
		}
		if good {
			i++
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
		d.trace = trace
		d.t = t
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
