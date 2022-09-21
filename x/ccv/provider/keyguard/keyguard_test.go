package keyguard

import (
	"math/rand"
	"testing"
)

type TraceState struct {
	Mapping      map[LK]FK
	LocalUpdates []update
	TP           int
	TC           int
	TM           int
}

type Driver struct {
	lastTP         int
	lastTC         int
	lastTM         int
	valSets        []map[LK]int
	mappings       []map[LK]FK
	foreignUpdates [][]update
}

func (d *Driver) runTrace(t *testing.T, trace []TraceState) {
	kg := KeyGuard{}

	d.lastTP = 0
	d.lastTC = 0
	d.lastTM = 0
	d.valSets = []map[LK]int{}
	d.mappings = []map[LK]FK{}
	d.foreignUpdates = [][]update{}

	init := trace[0]
	d.mappings = append(d.mappings, init.Mapping)
	for lk, fk := range init.Mapping {
		kg.SetForeignKey(lk, fk)
	}
	d.foreignUpdates = append(d.foreignUpdates, kg.ComputeUpdates(init.TP, init.LocalUpdates))
	d.valSets = append(d.valSets, map[LK]int{})
	for _, u := range init.LocalUpdates {
		d.valSets[0][u.key] = u.power
	}

	for _, s := range trace[1:] {
		if d.lastTP < s.TP {
			// TODO: impl all endblock shenanigans
			d.lastTP = s.TP
			d.mappings = append(d.mappings, s.Mapping)
			for lk, fk := range s.Mapping {
				kg.SetForeignKey(lk, fk)
			}
			d.foreignUpdates = append(d.foreignUpdates, kg.ComputeUpdates(s.TP, s.LocalUpdates))
		}
		if d.lastTC < s.TC {
			for i := d.lastTC + 1; i <= s.TC; i++ {
				// TODO: forward d.foreignUpdates[i] to the consumer logic
			}
			// use foreign updates ini range
			// TODO: do 'slash' checks
		}
		if d.lastTM < s.TM {
			// TODO: careful of meaning of TM because
			// it is initialised to 0 but actually 0 has not matured
			// TODO: prune up to TM
		}
		// TODO: check properties
	}
}

func getTrace() []TraceState {

	NUM_VALS := 3
	NUM_FKS := 9

	mapping := func() map[LK]FK {
		// TODO: currently I don't generate partial mappings but I might want to
		// Create a mapping of nums [0, NUM_VALS] mapped injectively to [0, NUM_FKS]
		ret := map[LK]FK{}
		good := func() bool {
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

	for i := 0; i < 100; i++ {
		choice := rand.Intn(3)
		if choice == 0 {
			ret = append(ret, TraceState{
				Mapping:      mapping(),
				LocalUpdates: localUpdates(),
				TP:           ret[i].TP + 1,
				TC:           ret[i].TC,
				TM:           ret[i].TM,
			})
		}
		if choice == 1 {
			curr := ret[i].TC
			limInclusive := ret[i].TP
			if curr < limInclusive {
				// add in [1, limInclusive - curr]
				// rand in [0, limInclusive - curr - 1]
				// bound is [0, limInclusive - curr)
				newTC := rand.Intn(limInclusive-curr) + curr + 1
				if newTC <= curr || limInclusive < curr {
					panic("bad choice 1")
				}
				ret = append(ret, TraceState{
					Mapping:      ret[i].Mapping,
					LocalUpdates: ret[i].LocalUpdates,
					TP:           ret[i].TP,
					TC:           newTC,
					TM:           ret[i].TM,
				})
			}
		}
		if choice == 2 {
			curr := ret[i].TM
			limInclusive := ret[i].TC
			if curr < limInclusive {
				newTM := rand.Intn(limInclusive-curr) + curr + 1
				if newTM <= curr || limInclusive < curr {
					panic("bad choice 2")
				}
				ret = append(ret, TraceState{
					Mapping:      ret[i].Mapping,
					LocalUpdates: ret[i].LocalUpdates,
					TP:           ret[i].TP,
					TC:           ret[i].TC,
					TM:           newTM,
				})
			}
		}
	}
	return ret
}

func TestPrototype(t *testing.T) {
	trace := []TraceState{}
	for len(trace) < 2 {
		trace = getTrace()
	}
	d := Driver{}
	d.runTrace(t, trace)
}

func TestKeyDelegation(t *testing.T) {
	traces := [][]TraceState{}
	for _, trace := range traces {
		d := Driver{}
		d.runTrace(t, trace)
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
