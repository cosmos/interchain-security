package keydel

import (
	"math/rand"
	"testing"

	"github.com/stretchr/testify/require"
)

const NUM_TRACES = 1000
const TRACE_LEN = 1000
const NUM_VALS = 4
const NUM_FKS = 50

type keyMapEntry struct {
	lk LK
	fk FK
}

type traceState struct {
	mapInstructions []keyMapEntry
	localUpdates    []update
	tp              int
	tc              int
	tm              int
}

type driver struct {
	t      *testing.T
	kd     *KeyDel
	trace  []traceState
	lastTP int
	lastTC int
	lastTM int
	// indexed by time (starting at 0)
	mappings []map[LK]FK
	// indexed by time (starting at 0)
	foreignUpdates [][]update
	// indexed by time (starting at 0)
	localValSets  []valSet
	foreignValSet valSet
}

func makeDriver(t *testing.T, trace []traceState) driver {
	d := driver{}
	d.t = t
	e := MakeKeyDel()
	d.kd = &e
	d.trace = trace
	d.lastTP = 0
	d.lastTC = 0
	d.lastTM = 0
	d.mappings = []map[LK]FK{}
	d.foreignUpdates = [][]update{}
	d.localValSets = []valSet{}
	d.foreignValSet = valSet{}
	return d
}

type valSet struct {
	keyToPower map[int]int
}

func makeValSet() valSet {
	return valSet{keyToPower: map[int]int{}}
}

func (vs *valSet) applyUpdates(updates []update) {
	for _, u := range updates {
		delete(vs.keyToPower, u.key)
		if 0 < u.power {
			vs.keyToPower[u.key] = u.power
		}
	}
}

func (d *driver) applyMapInstructions(instructions []keyMapEntry) {
	for _, instruction := range instructions {
		_ = d.kd.SetLocalToForeign(instruction.lk, instruction.fk)
	}
	copy := map[LK]FK{}
	for lk, fk := range d.kd.lkToFk {
		copy[lk] = fk
	}
	d.mappings = append(d.mappings, copy)
}

func (d *driver) applyLocalUpdates(localUpdates []update) {
	valSet := makeValSet()
	for lk, power := range d.localValSets[d.lastTP].keyToPower {
		valSet.keyToPower[lk] = power
	}
	valSet.applyUpdates(localUpdates)
	d.localValSets = append(d.localValSets, valSet)
}

func (d *driver) run() {

	{
		init := d.trace[0]
		// Set the initial map
		d.applyMapInstructions(init.mapInstructions)
		// Set the initial local set
		d.localValSets = append(d.localValSets, makeValSet())
		d.localValSets[init.tp].applyUpdates(init.localUpdates)
		// Set the initial foreign set
		d.foreignUpdates = append(d.foreignUpdates, d.kd.ComputeUpdates(init.tp, init.localUpdates))
		// The first foreign set equal to the local set at time 0
		d.foreignValSet = makeValSet()
		d.foreignValSet.applyUpdates(d.foreignUpdates[init.tc])
		d.kd.Prune(init.tm)
	}

	// Sanity check the initial state
	require.Len(d.t, d.mappings, 1)
	require.Len(d.t, d.foreignUpdates, 1)
	require.Len(d.t, d.localValSets, 1)

	// Check properties for each state after the initial
	for _, s := range d.trace[1:] {
		if d.lastTP < s.tp {
			// Provider time increment:
			// Apply some key mappings and create some new validator power updates
			d.applyMapInstructions(s.mapInstructions)
			d.applyLocalUpdates(s.localUpdates)
			d.foreignUpdates = append(d.foreignUpdates, d.kd.ComputeUpdates(s.tp, s.localUpdates))
			d.lastTP = s.tp
		}
		if d.lastTC < s.tc {
			for j := d.lastTC + 1; j <= s.tc; j++ {
				d.foreignValSet.applyUpdates(d.foreignUpdates[j])
			}
			d.lastTC = s.tc
		}
		if d.lastTM < s.tm {
			// Models maturations being received on the provider.
			d.kd.Prune(s.tm)
			d.lastTM = s.tm
		}
		require.True(d.t, d.kd.internalInvariants())
		d.checkProperties()
	}
}

func (d *driver) checkProperties() {

	/*
		When a consumer receives and processes up to VSCID i,
		it must have a validator set equal to that on the provider at i
		mapped through the key mapping that was on the provider when i
		was sent.
	*/
	validatorSetReplication := func() {

		// Get the current consumer val set.
		foreignSet := d.foreignValSet.keyToPower
		// Get the provider set at the corresponding time.
		localSet := d.localValSets[d.lastTC].keyToPower

		// Compute a lookup mapping consumer powers
		// back to provider powers, to enable comparison.
		foreignSetAsLocal := map[LK]int{}
		{
			mapping := d.mappings[d.lastTC]
			inverseMapping := map[FK]LK{}
			for lk, fk := range mapping {
				inverseMapping[fk] = lk
			}
			for fk, power := range foreignSet {
				foreignSetAsLocal[inverseMapping[fk]] = power
			}
		}

		// Ensure that the sets match exactly
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

		1. (Consumer Initiated Slashing Property) If a foreign key IS used in an update
		   for the consumer, with a positive power, at VSCID i, and no 0 power update
		   follows, then the local key associated to it must be queryable.
		   Phrased another way: foreign keys which are known to the consumer must be
		   useable for slashing indefinitely.
		2. (Pruning) If a foreign key IS NOT used in an update for a VSCID j with i < j,
		   and i is a 0 power update and has matured, then the foreign key is deleted
		   from storage.
		   Phrased another way: if the last 0 power update has matured, the key should
		   be pruned.
	*/
	pruning := func() {
		expectQueryable := map[FK]bool{}

		for i := 0; i <= d.lastTM; i++ {
			for _, u := range d.foreignUpdates[i] {
				expectQueryable[u.key] = 0 < u.power
			}
		}
		for i := d.lastTM + 1; i <= d.lastTP; i++ {
			for _, u := range d.foreignUpdates[i] {
				expectQueryable[u.key] = true
			}
		}
		for _, fk := range d.kd.lkToFk {
			expectQueryable[fk] = true
		}

		// Simply check every foreign key for the correct queryable-ness.
		for fk := 0; fk < NUM_FKS; fk++ {
			_, err := d.kd.GetLocal(fk)
			actualQueryable := err == nil
			if expect, found := expectQueryable[fk]; found && expect {
				require.True(d.t, actualQueryable)
			} else {
				require.False(d.t, actualQueryable)
			}
		}
	}

	/*
		TODO:
	*/
	queries := func() {
		// For each fk known to the consumer
		for consumerFK := range d.foreignValSet.keyToPower {
			queriedLK, err := d.kd.GetLocal(consumerFK)
			// There must be a corresponding local key
			require.Nil(d.t, err)
			providerFKs := map[FK]bool{}
			// The local key must be the one that was actually referenced
			// in the latest mapping used to compute updates sent to the
			// consumer.
			mapping := d.mappings[d.lastTC]
			for providerLK, providerFK := range mapping {
				require.Falsef(d.t, providerFKs[providerFK], "two local keys map to the same foreign key")
				providerFKs[providerFK] = true
				if consumerFK == providerFK {
					// A mapping to the consumer FK was found
					// The corresponding LK must be the one queried.
					require.Equal(d.t, providerLK, queriedLK)
				}
			}
			// Check that the comparison was actually made!
			require.Truef(d.t, providerFKs[consumerFK], "no mapping found for foreign key")
		}
	}

	validatorSetReplication()
	pruning()
	queries()

}

func getTrace(t *testing.T) []traceState {

	mappings := func() []keyMapEntry {
		ret := []keyMapEntry{}
		// Go several times to have overlapping validator updates
		for i := 0; i < 2; i++ {
			// include 0 to all validators
			include := rand.Intn(NUM_VALS + 1)
			for _, lk := range rand.Perm(NUM_VALS)[0:include] {
				ret = append(ret, keyMapEntry{lk, rand.Intn(NUM_FKS)})
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

	initialMappings := []keyMapEntry{}
	for i := 0; i < NUM_VALS; i++ {
		initialMappings = append(initialMappings, keyMapEntry{i, i})
	}

	ret := []traceState{
		{
			// Hard code initial mapping
			mapInstructions: initialMappings,
			localUpdates:    localUpdates(),
			tp:              0,
			tc:              0,
			tm:              0,
		},
	}

	for i := 0; i < TRACE_LEN; i++ {
		choice := rand.Intn(3)
		last := ret[len(ret)-1]
		if choice == 0 {
			ret = append(ret, traceState{
				mapInstructions: mappings(),
				localUpdates:    localUpdates(),
				tp:              last.tp + 1,
				tc:              last.tc,
				tm:              last.tm,
			})
		}
		if choice == 1 {
			curr := last.tc
			limInclusive := last.tp
			if curr < limInclusive {
				// add in [1, limInclusive - curr]
				// rand in [0, limInclusive - curr - 1]
				// bound is [0, limInclusive - curr)
				newTC := rand.Intn(limInclusive-curr) + curr + 1
				require.True(t, curr < newTC && curr <= limInclusive)
				ret = append(ret, traceState{
					mapInstructions: nil,
					localUpdates:    nil,
					tp:              last.tp,
					tc:              newTC,
					tm:              last.tm,
				})
			}
		}
		if choice == 2 {
			curr := last.tm
			limInclusive := last.tc
			if curr < limInclusive {
				newTM := rand.Intn(limInclusive-curr) + curr + 1
				require.True(t, curr < newTM && curr <= limInclusive)
				ret = append(ret, traceState{
					mapInstructions: nil,
					localUpdates:    nil,
					tp:              last.tp,
					tc:              last.tc,
					tm:              newTM,
				})
			}
		}
	}
	return ret
}

func TestRandomHeuristic(t *testing.T) {
	for i := 0; i < NUM_TRACES; i++ {
		trace := []traceState{}
		for len(trace) < 2 {
			trace = getTrace(t)
		}
		d := makeDriver(t, trace)
		d.run()
	}
}
