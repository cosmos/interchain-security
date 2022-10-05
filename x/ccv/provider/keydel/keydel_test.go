package keydel

import (
	"math/rand"
	"testing"

	"github.com/stretchr/testify/require"
)

// Num traces to run for heuristic testing
const NUM_TRACES = 1000

// Len of trace for a single heuristic testing run
const TRACE_LEN = 1000

// Number of validators to simulate
const NUM_VALS = 4

// Number of foreign keys in the universe
// (This is constrained to ensure overlap edge cases are tested)
const NUM_FKS = 50

type keyMapEntry struct {
	pk PK
	ck CK
}

type traceStep struct {
	keyMapEntries   []keyMapEntry
	providerUpdates []update
	timeProvider    int
	timeConsumer    int
	timeMaturity    int
}

type driver struct {
	t                *testing.T
	kd               *KeyDel
	trace            []traceStep
	lastTimeProvider int
	lastTimeConsumer int
	lastTimeMaturity int
	// indexed by time (starting at 0)
	mappings []map[PK]CK
	// indexed by time (starting at 0)
	consumerUpdates [][]update
	// indexed by time (starting at 0)
	localValSets []valSet
	// The validator set from the perspective of
	// the consumer chain.
	foreignValSet valSet
}

func makeDriver(t *testing.T, trace []traceStep) driver {
	d := driver{}
	d.t = t
	kd := MakeKeyDel()
	d.kd = &kd
	d.trace = trace
	d.lastTimeProvider = 0
	d.lastTimeConsumer = 0
	d.lastTimeMaturity = 0
	d.mappings = []map[PK]CK{}
	d.consumerUpdates = [][]update{}
	d.localValSets = []valSet{}
	d.foreignValSet = valSet{}
	return d
}

// Utility struct to make simulating a validator set easier.
type valSet struct {
	keyToPower map[int]int
}

func makeValSet() valSet {
	return valSet{keyToPower: map[int]int{}}
}

// Apply a batch of (key, power) updates to the known validator set.
func (vs *valSet) applyUpdates(updates []update) {
	for _, u := range updates {
		delete(vs.keyToPower, u.key)
		if 0 < u.power {
			vs.keyToPower[u.key] = u.power
		}
	}
}

// Apply a list of (pk, ck) mapping requests to the KeyDel class instance
func (d *driver) applyKeyMapEntries(entries []keyMapEntry) {
	for _, e := range entries {
		// TRY to map provider key pk to consumer key ck.
		// (May fail due to API constraints, this is correct)
		_ = d.kd.SetProviderKeyToConsumerKey(e.pk, e.ck)
	}
	// Duplicate the mapping for referencing later in tests.
	copy := map[PK]CK{}
	for lk, fk := range d.kd.pkToCk {
		copy[lk] = fk
	}
	d.mappings = append(d.mappings, copy)
}

// Apply a list of provider validator power updates
func (d *driver) applyProviderUpdates(providerUPdates []update) {
	// Duplicate the previous valSet so that it can be referenced
	// later in tests.
	valSet := makeValSet()
	for pk, power := range d.localValSets[d.lastTimeProvider].keyToPower {
		valSet.keyToPower[pk] = power
	}
	valSet.applyUpdates(providerUPdates)
	d.localValSets = append(d.localValSets, valSet)
}

// Run a trace
// This includes bootstrapping the data structure with the first (init)
// step of the trace, and running a sequence of steps afterwards.
// Internal and external invariants (properties) of the data structure
// are tested after each step.
func (d *driver) run() {

	// Initialise
	{
		init := d.trace[0]
		// Set the initial map
		d.applyKeyMapEntries(init.keyMapEntries)
		// Set the initial local set
		d.localValSets = append(d.localValSets, makeValSet())
		d.localValSets[init.timeProvider].applyUpdates(init.providerUpdates)
		// Set the initial foreign set
		d.consumerUpdates = append(d.consumerUpdates, d.kd.ComputeUpdates(init.timeProvider, init.providerUpdates))
		// The first foreign set equal to the local set at time 0
		d.foreignValSet = makeValSet()
		d.foreignValSet.applyUpdates(d.consumerUpdates[init.timeConsumer])
		d.kd.PruneUnusedKeys(init.timeMaturity)
	}

	// Sanity check the initial state
	require.Len(d.t, d.mappings, 1)
	require.Len(d.t, d.consumerUpdates, 1)
	require.Len(d.t, d.localValSets, 1)

	// Check properties for each step after the initial one
	for _, s := range d.trace[1:] {
		if d.lastTimeProvider < s.timeProvider {
			// Provider time increase:
			// Apply some new key mapping requests to KeyDel, and create new validator
			// power updates.
			d.applyKeyMapEntries(s.keyMapEntries)
			d.applyProviderUpdates(s.providerUpdates)
			// Store the updates, to reference later in tests.
			d.consumerUpdates = append(d.consumerUpdates, d.kd.ComputeUpdates(s.timeProvider, s.providerUpdates))
			d.lastTimeProvider = s.timeProvider
		}
		if d.lastTimeConsumer < s.timeConsumer {
			// Consumer time increase:
			// For each unit of time that has passed since the last increase, apply
			// any updates which have been 'emitted' by a provider time increase step.
			for j := d.lastTimeConsumer + 1; j <= s.timeConsumer; j++ {
				d.foreignValSet.applyUpdates(d.consumerUpdates[j])
			}
			d.lastTimeConsumer = s.timeConsumer
		}
		if d.lastTimeMaturity < s.timeMaturity {
			// Maturity time increase:
			// For each unit of time that has passed since the last increase,
			// a maturity is 'available'. We test batch maturity.
			d.kd.PruneUnusedKeys(s.timeMaturity)
			d.lastTimeMaturity = s.timeMaturity
		}

		// Do checks
		require.True(d.t, d.kd.internalInvariants())
		d.externalInvariants()
	}
}

// Check invariants which are 'external' to the data structure being used.
// That is: these invariants make sense in the context of the wider system,
// and aren't specifically about the KeyDel data structure internal state.
//
// There are three invariants
//
//  1. Validator Set Replication
//     'All consumer validator sets are some earlier provider validator set'
//
//  2. Queries
//     'It is always possible to query the provider key for a given consumer
//     key, when the consumer can still make slash requests'
//
//  3. Pruning
//     'When the pruning method is used correctly, the internal state of the
//     data structure does not grow unboundedly'
//
//     Please see body for details.
func (d *driver) externalInvariants() {

	/*
		For a consumer who has received updates up to vscid i, its
		local validator set must be equal to the set on the provider
		when i was sent, mapped through the mapping at that time.
	*/
	validatorSetReplication := func() {

		// Get the consumer set.
		cSet := d.foreignValSet.keyToPower
		// Get the provider set - at the corresponding time.
		pSet := d.localValSets[d.lastTimeConsumer].keyToPower

		// Compute a reverse lookup allowing comparison
		// of the two sets.
		cSetLikePSet := map[PK]int{}
		{
			mapping := d.mappings[d.lastTimeConsumer]
			inverseMapping := map[CK]PK{}
			for pk, ck := range mapping {
				inverseMapping[ck] = pk
			}
			for ck, power := range cSet {
				cSetLikePSet[inverseMapping[ck]] = power
			}
		}

		// Check that the two validator sets match exactly.
		for pk, expectedPower := range pSet {
			actualPower := cSetLikePSet[pk]
			require.Equal(d.t, expectedPower, actualPower)
		}
		for pk, actualPower := range cSetLikePSet {
			expectedPower := pSet[pk]
			require.Equal(d.t, expectedPower, actualPower)
		}
	}

	/*
		TODO:
	*/
	queries := func() {
		// For each fk known to the consumer
		for consumerFK := range d.foreignValSet.keyToPower {
			queriedLK, err := d.kd.GetProviderKey(consumerFK)
			// There must be a corresponding local key
			require.Nil(d.t, err)
			providerFKs := map[CK]bool{}
			// The local key must be the one that was actually referenced
			// in the latest mapping used to compute updates sent to the
			// consumer.
			mapping := d.mappings[d.lastTimeConsumer]
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
		expectQueryable := map[CK]bool{}

		for i := 0; i <= d.lastTimeMaturity; i++ {
			for _, u := range d.consumerUpdates[i] {
				expectQueryable[u.key] = 0 < u.power
			}
		}
		for i := d.lastTimeMaturity + 1; i <= d.lastTimeProvider; i++ {
			for _, u := range d.consumerUpdates[i] {
				expectQueryable[u.key] = true
			}
		}
		for _, fk := range d.kd.pkToCk {
			expectQueryable[fk] = true
		}

		// Simply check every foreign key for the correct queryable-ness.
		for fk := 0; fk < NUM_FKS; fk++ {
			_, err := d.kd.GetProviderKey(fk)
			actualQueryable := err == nil
			if expect, found := expectQueryable[fk]; found && expect {
				require.True(d.t, actualQueryable)
			} else {
				require.False(d.t, actualQueryable)
			}
		}
	}

	validatorSetReplication()
	queries()
	pruning()

}

// Return a randomly generated list of steps
// which can be used to execute actions for testing.
func getTrace(t *testing.T) []traceStep {

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

	ret := []traceStep{
		{
			// Hard code initial mapping
			keyMapEntries:   initialMappings,
			providerUpdates: localUpdates(),
			timeProvider:    0,
			timeConsumer:    0,
			timeMaturity:    0,
		},
	}

	for i := 0; i < TRACE_LEN; i++ {
		choice := rand.Intn(3)
		last := ret[len(ret)-1]
		if choice == 0 {
			ret = append(ret, traceStep{
				keyMapEntries:   mappings(),
				providerUpdates: localUpdates(),
				timeProvider:    last.timeProvider + 1,
				timeConsumer:    last.timeConsumer,
				timeMaturity:    last.timeMaturity,
			})
		}
		if choice == 1 {
			curr := last.timeConsumer
			limInclusive := last.timeProvider
			if curr < limInclusive {
				// add in [1, limInclusive - curr]
				// rand in [0, limInclusive - curr - 1]
				// bound is [0, limInclusive - curr)
				newTC := rand.Intn(limInclusive-curr) + curr + 1
				require.True(t, curr < newTC && curr <= limInclusive)
				ret = append(ret, traceStep{
					keyMapEntries:   nil,
					providerUpdates: nil,
					timeProvider:    last.timeProvider,
					timeConsumer:    newTC,
					timeMaturity:    last.timeMaturity,
				})
			}
		}
		if choice == 2 {
			curr := last.timeMaturity
			limInclusive := last.timeConsumer
			if curr < limInclusive {
				newTM := rand.Intn(limInclusive-curr) + curr + 1
				require.True(t, curr < newTM && curr <= limInclusive)
				ret = append(ret, traceStep{
					keyMapEntries:   nil,
					providerUpdates: nil,
					timeProvider:    last.timeProvider,
					timeConsumer:    last.timeConsumer,
					timeMaturity:    newTM,
				})
			}
		}
	}
	return ret
}

// Execute randomly generated traces (lists of actions)
// against new instances of the class, checking properties
// after each action is done.
func TestPropertiesRandomlyHeuristically(t *testing.T) {
	for i := 0; i < NUM_TRACES; i++ {
		trace := []traceStep{}
		for len(trace) < 2 {
			trace = getTrace(t)
		}
		d := makeDriver(t, trace)
		d.run()
	}
}
