package keeper_test

import (
	"math/rand"
	"testing"

	"github.com/stretchr/testify/require"

	sdktypes "github.com/cosmos/cosmos-sdk/types"

	testcrypto "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"

	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

func key(seed int) tmprotocrypto.PublicKey {
	v := testcrypto.NewCryptoIdentityFromIntSeed(seed)
	return v.TMProtoCryptoPublicKey()
}

// Num traces to run for heuristic testing
// About 1.5 secs per trace when using real store
const NUM_TRACES = 200

// Len of trace for a single heuristic testing run
const TRACE_LEN = 400

// Number of validators to simulate
const NUM_VALS = 8

// Number of consumer keys in the universe
// (This is constrained to ensure overlap edge cases are tested)
const NUM_CKS = 24

type keyAssignmentEntry struct {
	pk providerkeeper.ProviderKey
	ck providerkeeper.ConsumerKey
}

type traceStep struct {
	keyAssignmentEntries []keyAssignmentEntry
	providerUpdates      []abci.ValidatorUpdate
	timeProvider         int
	timeConsumer         int
	timeMaturity         int
}

type driver struct {
	t                *testing.T
	ka               *providerkeeper.KeyAssignment
	trace            []traceStep
	lastTimeProvider int
	lastTimeConsumer int
	lastTimeMaturity int
	// A historical record of assignments, it is used for checking
	// temporal properties.
	// indexed by a unit of time (starting at 0)
	assignments []map[string]providerkeeper.ConsumerKey
	// Another historical record.
	// indexed by a unit of time (starting at 0)
	consumerUpdates [][]abci.ValidatorUpdate
	// Another historical record.
	// indexed by a unit of time (starting at 0)
	providerValsets []valset
	// The validator set from the perspective of
	// the consumer chain.
	consumerValset valset
}

func newTestKeyAssignment(t *testing.T) *providerkeeper.KeyAssignment {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	chainID := "foobar"
	ka := providerkeeper.KeyAssignment{keeperParams.Ctx.KVStore(keeperParams.StoreKey), chainID}
	return &ka
}

type valset = []abci.ValidatorUpdate

func makeDriver(t *testing.T, trace []traceStep) driver {
	d := driver{}
	d.t = t
	d.ka = newTestKeyAssignment(t)
	d.trace = trace
	d.lastTimeProvider = 0
	d.lastTimeConsumer = 0
	d.lastTimeMaturity = 0
	d.assignments = []map[string]providerkeeper.ConsumerKey{}
	d.consumerUpdates = [][]abci.ValidatorUpdate{}
	d.providerValsets = []valset{}
	d.consumerValset = valset{}
	return d
}

// Apply a list of (pk, ck) assignment requests to the KeyDel class instance
func (d *driver) applyKeyAssignmentEntries(entries []keyAssignmentEntry) {
	for _, e := range entries {
		// TRY to map provider key pk to consumer key ck.
		// (May fail due to API constraints, this is correct)
		_ = d.ka.SetProviderPubKeyToConsumerPubKey(e.pk, e.ck)
	}
	// Duplicate the assignment for referencing later in tests.
	copy := map[string]providerkeeper.ConsumerKey{}
	d.ka.IterateProviderAddrToConsumerKey(func(pca providerkeeper.ProviderAddr, ck providerkeeper.ConsumerKey) bool {
		copy[string(pca)] = ck
		return false
	})
	d.assignments = append(d.assignments, copy)
}

// Apply a batch of (key, power) updates to the known validator set.
func applyUpdates(old valset, updates []abci.ValidatorUpdate) valset {
	new := valset{}
	for _, uExist := range old {
		shouldAdd := true
		for _, uUpdate := range updates {
			if uExist.PubKey.Equal(uUpdate.PubKey) {
				if 0 < uUpdate.Power {
					new = append(new, uUpdate)
				}
				shouldAdd = false
			}
		}
		if shouldAdd {
			new = append(new, uExist)
		}
	}
	return new
}

// Apply a list of provider validator power updates
func (d *driver) applyProviderUpdates(providerUpdates []abci.ValidatorUpdate) {
	// Duplicate the previous valSet so that it can be referenced
	// later in tests.
	valSet := append(valset{}, d.providerValsets[d.lastTimeProvider]...)
	valSet = applyUpdates(valSet, providerUpdates)
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
		d.applyKeyAssignmentEntries(init.keyAssignmentEntries)
		// Set the initial provider set
		d.providerValsets = append(d.providerValsets, applyUpdates(valset{}, init.providerUpdates))
		// Set the initial consumer set
		d.consumerUpdates = append(d.consumerUpdates, d.ka.ComputeUpdates(uint64(init.timeProvider), init.providerUpdates))
		// The first consumer set equal to the provider set at time 0
		d.consumerValset = applyUpdates(valset{}, d.consumerUpdates[init.timeConsumer])
		d.ka.PruneUnusedKeys(uint64(init.timeMaturity))
	}

	// Sanity check the initial state
	require.Len(d.t, d.assignments, 1)
	require.Len(d.t, d.consumerUpdates, 1)
	require.Len(d.t, d.providerValsets, 1)

	// Check properties for each step after the initial one
	for _, s := range d.trace[1:] {
		if d.lastTimeProvider < s.timeProvider {
			// Provider time increase:
			// Apply some new key assignment requests to KeyDel, and create new validator
			// power updates.
			d.applyKeyAssignmentEntries(s.keyAssignmentEntries)
			d.applyProviderUpdates(s.providerUpdates)

			// Store the updates, to reference later in tests.
			d.consumerUpdates = append(d.consumerUpdates, d.ka.ComputeUpdates(uint64(s.timeProvider), s.providerUpdates))
			d.lastTimeProvider = s.timeProvider
		}
		if d.lastTimeConsumer < s.timeConsumer {
			// Consumer time increase:
			// For each unit of time that has passed since the last increase, apply
			// any updates which have been 'emitted' by a provider time increase step.
			for j := d.lastTimeConsumer + 1; j <= s.timeConsumer; j++ {
				d.consumerValset = applyUpdates(d.consumerValset, d.consumerUpdates[j])
			}
			d.lastTimeConsumer = s.timeConsumer
		}
		if d.lastTimeMaturity < s.timeMaturity {
			// Maturity time increase:
			// For each unit of time that has passed since the last increase,
			// a maturity is 'available'. We test batch maturity.
			d.ka.PruneUnusedKeys(uint64(s.timeMaturity))
			d.lastTimeMaturity = s.timeMaturity
		}

		// Do checks
		require.True(d.t, d.ka.InternalInvariants())
		d.externalInvariants()
	}
}

// Check invariants which are 'external' to the data structure being used.
// That is: these invariants make sense in the context of the wider system,
// and aren't specifically about the internal state of the data structure.
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
		For a consumer who has received updates up to and including vscid i,
		its provider validator set must be equal to the set on the provider
		when i was sent, mapped through the assignment at that time.
	*/
	validatorSetReplication := func() {

		// Get the provider set - at the corresponding time.
		pSet := d.providerValsets[d.lastTimeConsumer]
		// Get the consumer set.
		cSet := d.consumerValset

		// Check that the two validator sets match exactly.
		require.Equal(d.t, len(pSet), len(cSet))

		for _, u := range pSet {

			// Find the appropriate forward assignment
			pk := u.PubKey
			expectedPower := u.Power
			found := false
			ck := providerkeeper.ConsumerKey{}
			for k, v := range d.assignments[d.lastTimeConsumer] {
				if pk.Equal(k) {
					ck = v
				}
			}
			require.NotEqualf(d.t, ck, providerkeeper.ConsumerKey{}, "bad test, a assignment must exist")

			// Check that the mapped through validator has the correct power
			for _, u := range cSet {
				if u.PubKey.Equal(ck) {
					require.Equal(d.t, expectedPower, u.Power)
					found = true
				}
			}
			require.True(d.t, found)
		}
	}

	/*
		For all keys that are known to the consumer chain, it is
		possible to query the provider chain for corresponding
		provider key in order to do slashing.
	*/
	queries := func() {
		// For each key known to the consumer
		for _, u := range d.consumerValset {
			ckOnConsumer := u.PubKey

			// The query must return a result
			pkQueried, found := d.ka.GetProviderPubKeyFromConsumerPubKey(ckOnConsumer)
			require.True(d.t, found)
			pkQueriedByConsAddr, found := d.ka.GetProviderPubKeyFromConsumerConsAddress(utils.TMCryptoPublicKeyToConsAddr(ckOnConsumer))
			require.True(d.t, found)
			require.Equal(d.t, pkQueried, pkQueriedByConsAddr)

			// The provider key must be the one that was actually referenced
			// in the latest actualAssignment used to compute updates sent to the
			// consumer.
			ckWasActuallyMappedTo := map[providerkeeper.ConsumerKey]bool{}
			actualAssignment := d.assignments[d.lastTimeConsumer]
			for pk, ck := range actualAssignment {

				// Sanity check: no two provider keys should map to the same consumer key
				require.Falsef(d.t, ckWasActuallyMappedTo[ck], "two provider keys map to the same consumer key")

				// Record that this consumer key was indeed mapped to by some provider key
				// at time lastTimeConsumer
				ckWasActuallyMappedTo[ck] = true

				// If the consumer key is the one used as a query param
				if ckOnConsumer.Equal(ck) {
					// Then the provider key returned by the query must be exactly
					// the same one as was actually mapped to.
					require.Equal(d.t, pk, pkQueried)
				}
			}
			// Check that the comparison was actually made, and that the test
			// actually did something.
			good := false
			for ck := range ckWasActuallyMappedTo {
				if ck.Equal(ckOnConsumer) {
					good = true
				}
			}
			require.Truef(d.t, good, "no assignment found for consumer key")
		}
	}

	/*
		All keys that the consumer definitely cannot use as a parameter in
		a slash request must eventually be pruned from state.
		A consumer can still reference a key if the last abci.ValidatorUpdate it received
		for the key had a positive power associated to it, OR the last abci.ValidatorUpdate
		had a 0 power associated (deletion) but the maturity period for that
		abci.ValidatorUpdate has not yet elapsed on the consumer, and thus a corresponding
		maturity packet has not been sent to the provider.
	*/
	pruning := func() {

		// Do we expect to be able to query the provider key for a given consumer
		// key?
		expectQueryable := map[string]bool{}

		for i := 0; i <= d.lastTimeMaturity; i++ {
			for _, u := range d.consumerUpdates[i] {
				// If the latest abci.ValidatorUpdate for a given consumer key was dispatched
				// AND also matured since the last maturity, then
				// 1) if that abci.ValidatorUpdate was a positive power abci.ValidatorUpdate then no subsequent
				//    zero power abci.ValidatorUpdate can have matured. Thus the key should be
				//    queryable.
				// 2) if that abci.ValidatorUpdate was a zero positive power abci.ValidatorUpdate then the
				//    key should not be queryable unless it was used in a subsequent
				//    abci.ValidatorUpdate (see next block).
				expectQueryable[providerkeeper.DeterministicStringify(u.PubKey)] = 0 < u.Power
			}
		}
		for i := d.lastTimeMaturity + 1; i <= d.lastTimeProvider; i++ {
			for _, u := range d.consumerUpdates[i] {
				// If a positive OR zero power abci.ValidatorUpdate was RECENTLY received
				// for the consumer, then the key must be queryable.
				expectQueryable[providerkeeper.DeterministicStringify(u.PubKey)] = true
			}
		}

		// Simply check every consumer key for the correct queryable-ness.
		for ck := 0; ck < NUM_CKS; ck++ {
			cca := utils.TMCryptoPublicKeyToConsAddr(key(ck))
			_, actualQueryable := d.ka.GetProviderPubKeyFromConsumerConsAddress(cca)
			if expect, found := expectQueryable[providerkeeper.DeterministicStringify(key(ck))]; found && expect {
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

	keyAssignments := func() []keyAssignmentEntry {
		ret := []keyAssignmentEntry{}

		const NUM_ITS = 2 // Chosen arbitrarily/heuristically
		// Do this NUM_ITS times, to be able to generate conflicting assignments.
		// This is allowed by the KeyDel API, so it must be tested.
		for i := 0; i < NUM_ITS; i++ {
			// include none (to) all validators
			pks := rand.Perm(NUM_VALS)[0:rand.Intn(NUM_VALS+1)]
			for _, pk := range pks {
				ck := rand.Intn(NUM_CKS)
				ret = append(ret, keyAssignmentEntry{key(pk), key(ck)})
			}
		}
		return ret
	}

	providerUpdates := func() []abci.ValidatorUpdate {
		ret := []abci.ValidatorUpdate{}

		// include none (to) all validators
		pks := rand.Perm(NUM_VALS)[0:rand.Intn(NUM_VALS+1)]
		for _, pk := range pks {
			// Only three values are interesting
			// 0: deletion
			// 1: positive
			// 2: positive (change)
			power := int64(rand.Intn(3))
			ret = append(ret, abci.ValidatorUpdate{PubKey: key(pk), Power: power})
		}
		return ret
	}

	// Get an initial key assignment.
	// The real system may use some manual set defaults.
	initialAssignment := []keyAssignmentEntry{}
	for pk := 0; pk < NUM_VALS; pk++ {
		ck := pk
		initialAssignment = append(initialAssignment, keyAssignmentEntry{key(pk), key(ck)})
	}

	ret := []traceStep{
		{
			// Hard code initial assignment
			keyAssignmentEntries: initialAssignment,
			providerUpdates:      providerUpdates(),
			timeProvider:         0,
			timeConsumer:         0,
			timeMaturity:         0,
		},
	}

	for i := 0; i < TRACE_LEN; i++ {
		choice := rand.Intn(3)
		last := ret[len(ret)-1]
		if choice == 0 {
			// Increment provider time, and generate
			// new key assignments and validator updates.
			ret = append(ret, traceStep{
				keyAssignmentEntries: keyAssignments(),
				providerUpdates:      providerUpdates(),
				timeProvider:         last.timeProvider + 1,
				timeConsumer:         last.timeConsumer,
				timeMaturity:         last.timeMaturity,
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
					keyAssignmentEntries: nil,
					providerUpdates:      nil,
					timeProvider:         last.timeProvider,
					timeConsumer:         newTC,
					timeMaturity:         last.timeMaturity,
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
					keyAssignmentEntries: nil,
					providerUpdates:      nil,
					timeProvider:         last.timeProvider,
					timeConsumer:         last.timeConsumer,
					timeMaturity:         newTM,
				})
			}
		}
	}
	return ret
}

// Execute randomly generated traces (lists of actions)
// against new instances of the class, checking properties
// after each action is done.
func TestKeyAssignmentPropertiesRandomlyHeuristically(t *testing.T) {
	for i := 0; i < NUM_TRACES; i++ {
		trace := []traceStep{}
		for len(trace) < 2 {
			trace = getTrace(t)
		}
		d := makeDriver(t, trace)
		d.run()
	}
}

func TestKeyAssignmentSameSeedEquality(t *testing.T) {
	// Keys compare using Equal
	k0 := key(0)
	k1 := key(0)
	require.True(t, k0.Equal(k1))
	require.False(t, k0 == k1)
}

func TestKeyAssignmentKeySerialization(t *testing.T) {
	// Equal keys serialize to the same bytes
	k0 := key(0)
	k1 := key(0)

	bz0, err := k0.Marshal()
	require.NoError(t, err)
	bz1, err := k1.Marshal()
	require.NoError(t, err)

	require.Equal(t, len(bz0), len(bz1))
	for i := range bz0 {
		require.Equal(t, bz0[i], bz1[i])
	}
}
func TestKeyAssignmentDeterministicStringify(t *testing.T) {
	for i := 0; i < 100; i++ {
		k0 := key(i)
		k1 := key(i)
		require.True(t, providerkeeper.DeterministicStringify(k0) == providerkeeper.DeterministicStringify(k1))
	}
}

func TestKeyAssignmentKeyComparison(t *testing.T) {
	// Marshall a key
	k := key(0)
	bz, err := k.Marshal()
	require.Nil(t, err)

	// Deserialize the bytes
	other := tmprotocrypto.PublicKey{}
	err = other.Unmarshal(bz)
	require.Nil(t, err)

	// Equals method works!
	require.Equal(t, k, other)
	require.True(t, k.Equal(other))

	// == does not work!
	require.False(t, k == other)
	require.True(t, k != other)

	// Golang maps use == for comparison
	// https://go.dev/ref/spec#Comparison_operators
	// This means that we can't use a map to store keys directly

	// Use DeterministicStringify to implement map keys
	require.True(t, providerkeeper.DeterministicStringify(k) == providerkeeper.DeterministicStringify(other))
}

func TestKeyAssignmentSameSeedMapLength(t *testing.T) {
	// Demonstrates problem with using == for map keys
	k0 := key(0)
	k1 := key(0)
	m := map[tmprotocrypto.PublicKey]bool{}
	m[k0] = true
	m[k1] = true
	require.Equal(t, k0, k1)
	require.Len(t, m, 2)
}

func TestKeyAssignmentSetCurrentQueryWithIdenticalKey(t *testing.T) {
	ka := newTestKeyAssignment(t)
	err := ka.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	require.NoError(t, err)
	actual, _ := ka.GetCurrentConsumerPubKeyFromProviderPubKey(key(42)) // Queryable
	require.Equal(t, key(43), actual)
}

func TestKeyAssignmentSetCurrentQueryWithEqualKey(t *testing.T) {
	ka := newTestKeyAssignment(t)
	k := key(42)
	err := ka.SetProviderPubKeyToConsumerPubKey(k, key(43))
	require.NoError(t, err)

	kbz, err := k.Marshal()
	require.Nil(t, err)
	kEqual := tmprotocrypto.PublicKey{}
	err = kEqual.Unmarshal(kbz)
	require.Nil(t, err)

	actual, _ := ka.GetCurrentConsumerPubKeyFromProviderPubKey(kEqual) // Queryable
	require.Equal(t, key(43), actual)
}

func TestKeyAssignmentNoSetReverseQuery(t *testing.T) {
	ka := newTestKeyAssignment(t)
	_, found := ka.GetProviderPubKeyFromConsumerPubKey(key(43)) // Not queryable
	require.False(t, found)
}

func TestKeyAssignmentSetReverseQuery(t *testing.T) {
	ka := newTestKeyAssignment(t)
	err := ka.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	require.NoError(t, err)
	actual, _ := ka.GetProviderPubKeyFromConsumerPubKey(key(43)) // Queryable
	require.Equal(t, key(42), actual)
}

func TestKeyAssignmentSetUseReplaceAndReverse(t *testing.T) {
	ka := newTestKeyAssignment(t)
	err := ka.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	require.NoError(t, err)
	updates := []abci.ValidatorUpdate{{PubKey: key(42), Power: 999}}
	ka.ComputeUpdates(100, updates)
	err = ka.SetProviderPubKeyToConsumerPubKey(key(42), key(44)) // New consumer key
	require.NoError(t, err)
	actual, _ := ka.GetProviderPubKeyFromConsumerConsAddress(utils.TMCryptoPublicKeyToConsAddr(key(43)))
	require.Equal(t, key(42), actual)
	actual, _ = ka.GetProviderPubKeyFromConsumerPubKey(key(44)) // New is queryable
	require.Equal(t, key(42), actual)
	ka.ComputeUpdates(101, updates) // Old is no longer known to consumer
	ka.PruneUnusedKeys(102)         // Old is garbage collected on provider
	_, found := ka.GetProviderPubKeyFromConsumerConsAddress(utils.TMCryptoPublicKeyToConsAddr(key(43)))
	require.False(t, found)
	actual, _ = ka.GetProviderPubKeyFromConsumerPubKey(key(44)) // New key is still queryable
	require.Equal(t, key(42), actual)
}

func TestKeyAssignmentDelete(t *testing.T) {
	ka := newTestKeyAssignment(t)
	providerIdentity := testcrypto.NewCryptoIdentityFromIntSeed(42)
	consumerIdentity0 := testcrypto.NewCryptoIdentityFromIntSeed(43)
	consumerIdentity1 := testcrypto.NewCryptoIdentityFromIntSeed(44)
	pk := providerIdentity.TMProtoCryptoPublicKey()
	ck0 := consumerIdentity0.TMProtoCryptoPublicKey()
	ck1 := consumerIdentity1.TMProtoCryptoPublicKey()

	err := ka.SetProviderPubKeyToConsumerPubKey(pk, ck0)
	require.NoError(t, err)

	updates := []abci.ValidatorUpdate{{PubKey: pk, Power: 999}}
	ka.ComputeUpdates(100, updates)

	err = ka.SetProviderPubKeyToConsumerPubKey(pk, ck1) // New consumer key
	require.NoError(t, err)
	ka.ComputeUpdates(101, updates)

	ka.DeleteProviderKey(providerIdentity.SDKConsAddress())

	_, found := ka.GetCurrentConsumerPubKeyFromProviderPubKey(pk)
	require.False(t, found)
	_, found = ka.GetProviderPubKeyFromConsumerPubKey(ck0)
	require.False(t, found)
	_, found = ka.GetProviderPubKeyFromConsumerPubKey(ck1)
	require.False(t, found)
	_, found = ka.GetProviderPubKeyFromConsumerConsAddress(consumerIdentity0.SDKConsAddress())
	require.False(t, found)
	_, found = ka.GetProviderPubKeyFromConsumerConsAddress(consumerIdentity1.SDKConsAddress())
	require.False(t, found)
}

func TestKeyAssignmentSetUseReplaceAndPrune(t *testing.T) {
	ka := newTestKeyAssignment(t)
	err := ka.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	require.NoError(t, err)
	updates := []abci.ValidatorUpdate{{PubKey: key(42), Power: 999}}
	ka.ComputeUpdates(100, updates)
	err = ka.SetProviderPubKeyToConsumerPubKey(key(42), key(44))
	require.NoError(t, err)
	actual, _ := ka.GetProviderPubKeyFromConsumerConsAddress(utils.TMCryptoPublicKeyToConsAddr(key(43)))
	require.Equal(t, key(42), actual)
	actual, _ = ka.GetProviderPubKeyFromConsumerPubKey(key(44)) // Queryable
	require.Equal(t, key(42), actual)
	ka.PruneUnusedKeys(101) // Should not be pruned
	_, found := ka.GetProviderPubKeyFromConsumerConsAddress(utils.TMCryptoPublicKeyToConsAddr(key(43)))
	require.True(t, found)
	actual, _ = ka.GetProviderPubKeyFromConsumerPubKey(key(44)) // New key is still queryable
	require.Equal(t, key(42), actual)
}

func TestKeyAssignmentSetUnsetReverseQuery(t *testing.T) {
	ka := newTestKeyAssignment(t)
	err := ka.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	require.NoError(t, err)
	err = ka.SetProviderPubKeyToConsumerPubKey(key(42), key(44)) // Set to different value
	require.NoError(t, err)
	_, found := ka.GetProviderPubKeyFromConsumerPubKey(key(43)) // Ealier value not queryable
	require.False(t, found)
}

func TestKeyAssignmentGCUpdateIsEmitted(t *testing.T) {
	ka := newTestKeyAssignment(t)
	err := ka.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	require.NoError(t, err)
	updates := []abci.ValidatorUpdate{{PubKey: key(42), Power: 999}}
	ka.ComputeUpdates(100, updates)
	err = ka.SetProviderPubKeyToConsumerPubKey(key(42), key(44)) // Now use a different consumer key
	require.NoError(t, err)
	consumerUpdates := ka.ComputeUpdates(100, []abci.ValidatorUpdate{})
	good := false
	for _, u := range consumerUpdates {
		if u.PubKey.Equal(key(43)) {
			// There exists a garbage collecting update
			require.Equal(t, u.Power, int64(0))
			good = true
		}
	}
	require.True(t, good)
}

func TestValidatorRemoval(t *testing.T) {
	ka := newTestKeyAssignment(t)

	updates := []abci.ValidatorUpdate{{PubKey: key(42), Power: 999}}

	err := ka.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	require.NoError(t, err)
	ka.ComputeUpdates(0, updates)

	err = ka.SetProviderPubKeyToConsumerPubKey(key(42), key(44)) // Now use a different consumer key
	require.NoError(t, err)
	ka.ComputeUpdates(1, updates)

	err = ka.SetProviderPubKeyToConsumerPubKey(key(42), key(45)) // Now use a different consumer key
	require.NoError(t, err)
	ka.ComputeUpdates(2, updates)

	pca := utils.TMCryptoPublicKeyToConsAddr(key(42))
	ka.DeleteProviderKey(pca)

	_, found := ka.GetProviderAddrToConsumerKey(pca)
	require.False(t, found)
	_, found = ka.GetConsumerKeyToProviderKey(key(43))
	require.False(t, found)
	_, found = ka.GetConsumerKeyToProviderKey(key(44))
	require.False(t, found)
	_, found = ka.GetConsumerKeyToProviderKey(key(45))
	require.False(t, found)

	for i := 43; i < 46; i++ {
		_, found = ka.GetConsumerAddrToLastUpdateInfo(utils.TMCryptoPublicKeyToConsAddr(key(i)))
		require.False(t, found)

	}
	ka.IterateConsumerAddrToLastUpdateInfo(func(cca providerkeeper.ConsumerAddr, lum providertypes.LastUpdateInfo) bool {
		pcaQueried := utils.TMCryptoPublicKeyToConsAddr(*lum.ProviderKey)
		require.False(t, pca.Equals(pcaQueried))
		return false
	})

}

func compareForEquality(t *testing.T,
	ka providerkeeper.KeyAssignment,
	pcaToCk map[string]providerkeeper.ConsumerKey,
	ckToPk map[providerkeeper.ConsumerKey]providerkeeper.ProviderKey,
	ccaToLastUpdateMemo map[string]providertypes.LastUpdateInfo) {

	cnt := 0
	ka.IterateProviderAddrToConsumerKey(func(_ providerkeeper.ProviderAddr, _ providerkeeper.ConsumerKey) bool {
		cnt += 1
		return false
	})
	require.Equal(t, len(pcaToCk), cnt)

	cnt = 0
	ka.IterateConsumerKeyToProviderKey(func(_, _ providerkeeper.ConsumerKey) bool {
		cnt += 1
		return false
	})
	require.Equal(t, len(ckToPk), cnt)

	cnt = 0
	ka.IterateConsumerAddrToLastUpdateInfo(func(_ providerkeeper.ConsumerAddr, _ providertypes.LastUpdateInfo) bool {
		cnt += 1
		return false
	})
	require.Equal(t, len(ccaToLastUpdateMemo), cnt)

	for k, vExpect := range pcaToCk {
		vActual, found := ka.GetProviderAddrToConsumerKey(providerkeeper.ProviderAddr(k))
		require.True(t, found)
		require.Equal(t, vExpect, vActual)
	}
	for k, vExpect := range ckToPk {
		vActual, found := ka.GetConsumerKeyToProviderKey(k)
		require.True(t, found)
		require.Equal(t, vExpect, vActual)
	}
	for k, vExpect := range ccaToLastUpdateMemo {
		k := sdktypes.ConsAddress(k)
		m, found := ka.GetConsumerAddrToLastUpdateInfo(k)
		require.True(t, found)
		require.Equal(t, vExpect.ProviderKey, m.ProviderKey)
		require.Equal(t, vExpect.ConsumerKey, m.ConsumerKey)
		require.Equal(t, vExpect.Vscid, m.Vscid)
		require.Equal(t, vExpect.Power, m.Power)
	}

}

func checkCorrectSerializationAndDeserialization(t *testing.T,
	chainID string, keys []tmprotocrypto.PublicKey,
	string0 string,
	string1 string,
	string2 string,
	string3 string,
	int64_0 int64,
	int64_1 int64,
	uint64_0 uint64,
	uint64_1 uint64,
) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)

	pcaToCk := map[string]providerkeeper.ConsumerKey{}
	ckToPk := map[providerkeeper.ConsumerKey]providerkeeper.ProviderKey{}
	ccaToLastUpdateMemo := map[string]providertypes.LastUpdateInfo{}

	pcaToCk[string(utils.TMCryptoPublicKeyToConsAddr(keys[0]))] = keys[1]
	pcaToCk[string(utils.TMCryptoPublicKeyToConsAddr(keys[2]))] = keys[3]
	ckToPk[keys[4]] = keys[5]
	ckToPk[keys[6]] = keys[7]
	ccaToLastUpdateMemo[string(utils.TMCryptoPublicKeyToConsAddr(keys[8]))] = providertypes.LastUpdateInfo{
		ConsumerKey: &keys[9],
		ProviderKey: &keys[10],
		Vscid:       uint64_0,
		Power:       int64_0,
	}
	ccaToLastUpdateMemo[string(utils.TMCryptoPublicKeyToConsAddr(keys[11]))] = providertypes.LastUpdateInfo{
		ConsumerKey: &keys[12],
		ProviderKey: &keys[13],
		Vscid:       uint64_1,
		Power:       int64_1,
	}

	{
		// Use one KeyAssignment instance to serialize the data
		ka := providerkeeper.KeyAssignment{keeperParams.Ctx.KVStore(keeperParams.StoreKey), chainID}
		for k, v := range pcaToCk {
			ka.SetProviderAddrToConsumerKey(sdktypes.ConsAddress(k), v)
		}
		for k, v := range ckToPk {
			ka.SetConsumerKeyToProviderKey(k, v)
		}
		for k, v := range ccaToLastUpdateMemo {
			ka.SetConsumerAddrToLastUpdateInfo(sdktypes.ConsAddress(k), v)
		}
	}

	// Use another KeyAssignment instance to deserialize the data
	ka := providerkeeper.KeyAssignment{keeperParams.Ctx.KVStore(keeperParams.StoreKey), chainID}

	// Check that the data is the same

	compareForEquality(t, ka, pcaToCk, ckToPk, ccaToLastUpdateMemo)
}

func TestKeyAssignmentSerializationAndDeserialization(t *testing.T) {
	keys := []tmprotocrypto.PublicKey{}
	for i := 0; i < 16; i++ {
		keys = append(keys, key(i))
	}
	checkCorrectSerializationAndDeserialization(t, "foobar", keys,
		"string0",
		"string1",
		"string2",
		"string3",
		42,
		43,
		44,
		45,
	)
}
