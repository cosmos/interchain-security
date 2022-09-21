package keyguard

import (
	"math/rand"
	"testing"

	"github.com/stretchr/testify/require"
)

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
	kg := MakeKeyGuard()

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
		kg.SetLocalToForeign(lk, fk)
	}
	// Set the initial local set
	d.localValSets = append(d.localValSets, MakeValSet())
	d.localValSets[init.TP].processUpdates(init.LocalUpdates)
	// Set the initial foreign set
	d.foreignUpdates = append(d.foreignUpdates, kg.ComputeUpdates(init.TP, init.LocalUpdates))
	d.foreignValSet.processUpdates(d.foreignUpdates[init.TC])
	kg.Prune(init.TM)

	require.Len(d.t, d.mappings, 1)
	require.Len(d.t, d.foreignUpdates, 1)
	require.Len(d.t, d.localValSets, 1)

	for i, s := range d.trace {
		if i < 1 {
			continue
		}
		if d.lastTP < s.TP {
			d.mappings = append(d.mappings, s.Mapping)
			d.localValSets = append(d.localValSets, MakeValSet())
			for lk, power := range d.localValSets[i-1].keyToPower {
				d.localValSets[i].keyToPower[lk] = power
			}
			d.localValSets[i].processUpdates(s.LocalUpdates)
			d.lastTP = s.TP
			for lk, fk := range s.Mapping {
				kg.SetLocalToForeign(lk, fk)
			}
			d.foreignUpdates = append(d.foreignUpdates, kg.ComputeUpdates(s.TP, s.LocalUpdates))
		}
		if d.lastTC < s.TC {
			for j := d.lastTC + 1; j <= s.TC; j++ {
				d.foreignValSet.processUpdates(d.foreignUpdates[j])
			}
			d.lastTC = s.TC
		}
		if d.lastTM < s.TM {
			// TODO: check this because TM is initialised to 0 but 0 has not actually matured
			// TODO: I think one solution IS TO ACTUALLY prune 0 in init
			kg.Prune(s.TM)
			d.lastTM = s.TM
		}
		d.checkProperties()
	}
}

func (d *Driver) checkProperties() {
	// Check that the foreign ValSet is equal to the local ValSet
	// at time TC via inverse mapping
	foreignSet := d.foreignValSet.keyToPower
	localSet := d.localValSets[d.lastTC].keyToPower
	mapping := d.mappings[d.lastTC]
	inverseMapping := map[FK]LK{}
	for lk, fk := range mapping {
		inverseMapping[fk] = lk
	}
	foreignSetAsLocal := map[LK]int{}
	for fk, power := range foreignSet {
		foreignSetAsLocal[inverseMapping[fk]] = power
	}
	for lk, actual := range foreignSetAsLocal {
		expect := localSet[lk]
		require.Equal(d.t, expect, actual)
	}
	for lk, expect := range localSet {
		actual := foreignSetAsLocal[lk]
		require.Equal(d.t, expect, actual)
	}

	// TODO: check pruning and reverse queries
}

func getTrace(t *testing.T) []TraceState {

	TRACE_LEN := 3
	NUM_VALS := 3
	NUM_FKS := 9

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
				ret[lk] = -rand.Intn(NUM_FKS)
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

	rand.Seed(40)
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

func TestKeyDelegation(t *testing.T) {
	traces := [][]TraceState{}
	for _, trace := range traces {
		d := Driver{}
		d.trace = trace
		d.t = t
		d.runTrace()
	}
}

// TODO:

// These are the critical properties
// 1. All validator sets on consumer are a validator set for provider for an earlier
// time, mapped through the effective mapping at that time.
// 2. It is always possible to fetch a local key, given a foreign key, if the foreign
// key is still known to the consumer

// My thinking now is that I can test by doing the following
// If the trace TP increases than there is a new mapping and local updates
// the local updates aggregate to create a local validator set
// record that validator set, and the relevant mapping to time T=TP
// If TC increases to time T, can check the ACTUAL validator set in C
//	 It should be be possible to query kg for every validator foreign key
//    in any intermediate val set in [TM+1, TP]
// It should not be possible to query kg for any validator that does not appear
// 		in any intermediate vla set in [0, TM]
