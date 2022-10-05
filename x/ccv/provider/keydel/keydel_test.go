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

// Number of consumer keys in the universe
// (This is constrained to ensure overlap edge cases are tested)
const NUM_CKS = 50

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
	providerValsets []valset
	// The validator set from the perspective of
	// the consumer chain.
	consumerValsets valset
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
	d.providerValsets = []valset{}
	d.consumerValsets = valset{}
	return d
}

// Utility struct to make simulating a validator set easier.
type valset struct {
	keyToPower map[int]int
}

func makeValset() valset {
	return valset{keyToPower: map[int]int{}}
}

// Apply a batch of (key, power) updates to the known validator set.
func (vs *valset) applyUpdates(updates []update) {
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
	valSet := makeValset()
	for pk, power := range d.providerValsets[d.lastTimeProvider].keyToPower {
		valSet.keyToPower[pk] = power
	}
	valSet.applyUpdates(providerUPdates)
	d.providerValsets = append(d.providerValsets, valSet)
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
		// Set the initial provider set
		d.providerValsets = append(d.providerValsets, makeValset())
		d.providerValsets[init.timeProvider].applyUpdates(init.providerUpdates)
		// Set the initial consumer set
		d.consumerUpdates = append(d.consumerUpdates, d.kd.ComputeUpdates(init.timeProvider, init.providerUpdates))
		// The first consumer set equal to the provider set at time 0
		d.consumerValsets = makeValset()
		d.consumerValsets.applyUpdates(d.consumerUpdates[init.timeConsumer])
		d.kd.PruneUnusedKeys(init.timeMaturity)
	}

	// Sanity check the initial state
	require.Len(d.t, d.mappings, 1)
	require.Len(d.t, d.consumerUpdates, 1)
	require.Len(d.t, d.providerValsets, 1)

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
				d.consumerValsets.applyUpdates(d.consumerUpdates[j])
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
		provider validator set must be equal to the set on the provider
		when i was sent, mapped through the mapping at that time.
	*/
	validatorSetReplication := func() {

		// Get the consumer set.
		cSet := d.consumerValsets.keyToPower
		// Get the provider set - at the corresponding time.
		pSet := d.providerValsets[d.lastTimeConsumer].keyToPower

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
		For any key that the consumer is aware of, because it has
		received that key at some time in the past, and has not yet
		returned the maturity vscid for its removal:
		the key is useable as a query parameter to lookup the key
		of the validator which should be slashed for misbehavior.
	*/
	queries := func() {
		// For each key known to the consumer
		for ck := range d.consumerValsets.keyToPower {

			// The query must return a result
			pkQueried, err := d.kd.GetProviderKey(ck)
			require.Nil(d.t, err)

			// The provider key must be the one that was actually referenced
			// in the latest trueMapping used to compute updates sent to the
			// consumer.
			cks_TRUE := map[CK]bool{}
			trueMapping := d.mappings[d.lastTimeConsumer]
			for pk_TRUE, ck_TRUE := range trueMapping {

				// Sanity check: no two provider keys should map to the same consumer key
				require.Falsef(d.t, cks_TRUE[ck_TRUE], "two provider keys map to the same consumer key")

				// Record that this consumer key was indeed mapped to by some provider key
				// at time lastTimeConsumer
				cks_TRUE[ck_TRUE] = true

				// If the consumer key is the one used as a query param
				if ck == ck_TRUE {
					// Then the provider key returned by the query must be exactly
					// the same one as was actually mapped to.
					require.Equal(d.t, pk_TRUE, pkQueried)
				}
			}
			// Check that the comparison was actually made, and that the test
			// actually did something.
			require.Truef(d.t, cks_TRUE[ck], "no mapping found for consumer key")
		}
	}

	/*
		All keys that the consumer definitely cannot use as a parameter in
		a slash request must eventually be pruned from state.
		A consumer can still reference a key if the last update it received
		for the key had a positive power associated to it, OR the last update
		had a 0 power associated (deletion) but the maturity period for that
		update has not yet elapsed (and the maturity was not yet received
		on the provider chain).
	*/
	pruning := func() {

		// Do we expect to be able to query the provider key for a given consumer
		// key?
		expectQueryable := map[CK]bool{}

		for i := 0; i <= d.lastTimeMaturity; i++ {
			for _, u := range d.consumerUpdates[i] {
				// If the latest update for a given consumer key was dispatched
				// AND also matured since the last maturity, then
				// 1) if that update was a positive power update then no subsequent
				//    zero power update can have matured. Thus the key should be
				//    queryable.
				// 2) if that update was a zero positive power update then the
				//    key should not be queryable unless it was used in a subsquent
				//    update (see next block).
				expectQueryable[u.key] = 0 < u.power
			}
		}
		for i := d.lastTimeMaturity + 1; i <= d.lastTimeProvider; i++ {
			for _, u := range d.consumerUpdates[i] {
				// If a positive OR zero power update was RECENTLY received
				// for the consumer, then the key must be queryable.
				expectQueryable[u.key] = true
			}
		}
		// If a consumer key is CURRENTLY mapped to by a provider key, it
		// must be queryable.
		for _, ck := range d.kd.pkToCk {
			expectQueryable[ck] = true
		}

		// Simply check every consumer key for the correct queryable-ness.
		for ck := 0; ck < NUM_CKS; ck++ {
			_, err := d.kd.GetProviderKey(ck)
			actualQueryable := err == nil
			if expect, found := expectQueryable[ck]; found && expect {
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
	// TODO: check the hardcoded numbers

	keyMappings := func() []keyMapEntry {
		ret := []keyMapEntry{}

		const NUM_ITS = 2 // Chosen arbitrarily/heuristically
		// Do this NUM_ITS times, to be able to generate conflicting mappings.
		// This is allowed by the KeyDel API, so it must be tested.
		for i := 0; i < NUM_ITS; i++ {
			// include none (to) all validators
			pks := rand.Perm(NUM_VALS)[0:rand.Intn(NUM_VALS+1)]
			for _, pk := range pks {
				ck := rand.Intn(NUM_CKS)
				ret = append(ret, keyMapEntry{pk, ck})
			}
		}
		return ret
	}

	providerUpdates := func() []update {
		ret := []update{}

		// include none (to) all validators
		pks := rand.Perm(NUM_VALS)[0:rand.Intn(NUM_VALS+1)]
		for _, pk := range pks {
			// Only three values are interesting
			// 0: deletion
			// 1: positive
			// 2: positive (change)
			power := rand.Intn(3)
			ret = append(ret, update{key: pk, power: power})
		}
		return ret
	}

	// Get an initial key mapping.
	// The real system may use some manual set defaults.
	initialMappings := []keyMapEntry{}
	for i := 0; i < NUM_VALS; i++ {
		initialMappings = append(initialMappings, keyMapEntry{i, i})
	}

	ret := []traceStep{
		{
			// Hard code initial mapping
			keyMapEntries:   initialMappings,
			providerUpdates: providerUpdates(),
			timeProvider:    0,
			timeConsumer:    0,
			timeMaturity:    0,
		},
	}

	for i := 0; i < TRACE_LEN; i++ {
		choice := rand.Intn(3)
		last := ret[len(ret)-1]
		if choice == 0 {
			// Increment provider time, and generate
			// new key mappings and validator updates.
			ret = append(ret, traceStep{
				keyMapEntries:   keyMappings(),
				providerUpdates: providerUpdates(),
				timeProvider:    last.timeProvider + 1,
				timeConsumer:    last.timeConsumer,
				timeMaturity:    last.timeMaturity,
			})
		}
		if choice == 1 {
			// If possible, increase consumer time.
			// This models receiving VSC packets on the consumer.
			curr := last.timeConsumer
			limInclusive := last.timeProvider
			if curr < limInclusive {
				// add in [1, limInclusive - curr]
				// rand in [0, limInclusive - curr - 1]
				// bound is [0, limInclusive - curr)
				newTC := rand.Intn(limInclusive-curr) + curr + 1
				require.True(t, curr < newTC && newTC <= limInclusive)
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
			// If possible, increase maturity time.
			// This models sending maturities on the consumer (and also
			// receiving them on the provider).
			curr := last.timeMaturity
			limInclusive := last.timeConsumer
			if curr < limInclusive {
				newTM := rand.Intn(limInclusive-curr) + curr + 1
				require.True(t, curr < newTM && newTM <= limInclusive)
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
