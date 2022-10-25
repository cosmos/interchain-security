package keeper_test

import (
	cryptoEd25519 "crypto/ed25519"
	"encoding/binary"
	"math/rand"
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cosmosEd25519 "github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/ibc-go/v3/testing/mock"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

// TODO: all the map lookups are probably gonna fail because the objects are different

// Num traces to run for heuristic testing
// About 1.5 secs per trace when using real store
const NUM_TRACES = 4000

// Len of trace for a single heuristic testing run
const TRACE_LEN = 400

// Number of validators to simulate
const NUM_VALS = 4

// Number of consumer keys in the universe
// (This is constrained to ensure overlap edge cases are tested)
const NUM_CKS = 50

func fromSeed(seed []byte) crypto.PublicKey {
	//lint:ignore SA1019 We don't care because this is only a test.
	privKey := mock.PV{PrivKey: &cosmosEd25519.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}
	pubKey, err := privKey.GetPubKey()
	if err != nil {
		panic(err)
	}
	sdkVer, err := cryptocodec.FromTmPubKeyInterface(pubKey)
	if err != nil {
		panic(err)
	}
	pk, err := cryptocodec.ToTmProtoPublicKey(sdkVer)
	if err != nil {
		panic(err)
	}
	return pk
}

func key(i uint64) crypto.PublicKey {
	seed := []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	binary.LittleEndian.PutUint64(seed[:8], i)
	return fromSeed(seed)
}

type keyMapEntry struct {
	pk keeper.ProviderPubKey
	ck keeper.ConsumerPubKey
}

type traceStep struct {
	keyMapEntries   []keyMapEntry
	providerUpdates []abci.ValidatorUpdate
	timeProvider    int
	timeConsumer    int
	timeMaturity    int
}

type driver struct {
	t                *testing.T
	km               *keeper.KeyMap
	trace            []traceStep
	lastTimeProvider int
	lastTimeConsumer int
	lastTimeMaturity int
	// indexed by time (starting at 0)
	mappings []map[keeper.ProviderPubKey]keeper.ConsumerPubKey
	// indexed by time (starting at 0)
	consumerUpdates [][]abci.ValidatorUpdate
	// indexed by time (starting at 0)
	providerValsets []valset
	// The validator set from the perspective of
	// the consumer chain.
	consumerValset valset
}

func newTestKeyMap(t *testing.T) *keeper.KeyMap {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	chainID := "foobar"
	store := keeper.KeyMapStore{keeperParams.Ctx.KVStore(keeperParams.StoreKey), chainID}
	km := keeper.MakeKeyMap(&store)
	return &km
}

type valset = []abci.ValidatorUpdate

func makeDriver(t *testing.T, trace []traceStep) driver {
	d := driver{}
	d.t = t
	d.km = newTestKeyMap(t)
	d.trace = trace
	d.lastTimeProvider = 0
	d.lastTimeConsumer = 0
	d.lastTimeMaturity = 0
	d.mappings = []map[keeper.ProviderPubKey]keeper.ConsumerPubKey{}
	d.consumerUpdates = [][]abci.ValidatorUpdate{}
	d.providerValsets = []valset{}
	d.consumerValset = valset{}
	return d
}

// Apply a list of (pk, ck) mapping requests to the KeyDel class instance
func (d *driver) applyKeyMapEntries(entries []keyMapEntry) {
	for _, e := range entries {
		// TRY to map provider key pk to consumer key ck.
		// (May fail due to API constraints, this is correct)
		_ = d.km.SetProviderPubKeyToConsumerPubKey(e.pk, e.ck)
	}
	// Duplicate the mapping for referencing later in tests.
	copy := map[keeper.ProviderPubKey]keeper.ConsumerPubKey{}
	d.km.Store.IteratePkToCk(func(pk, ck keeper.ConsumerPubKey) bool {
		copy[pk] = ck
		return false
	})
	d.mappings = append(d.mappings, copy)
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
		d.applyKeyMapEntries(init.keyMapEntries)
		// Set the initial provider set
		d.providerValsets = append(d.providerValsets, applyUpdates(valset{}, init.providerUpdates))
		// Set the initial consumer set
		d.consumerUpdates = append(d.consumerUpdates, d.km.ComputeUpdates(uint64(init.timeProvider), init.providerUpdates))
		// The first consumer set equal to the provider set at time 0
		d.consumerValset = applyUpdates(valset{}, d.consumerUpdates[init.timeConsumer])
		d.km.PruneUnusedKeys(uint64(init.timeMaturity))
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
			d.consumerUpdates = append(d.consumerUpdates, d.km.ComputeUpdates(uint64(s.timeProvider), s.providerUpdates))
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
			d.km.PruneUnusedKeys(uint64(s.timeMaturity))
			d.lastTimeMaturity = s.timeMaturity
		}

		// Do checks
		require.True(d.t, d.km.InternalInvariants())
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
//
// TODO: check invariant wording precision
func (d *driver) externalInvariants() {

	/*
		For a consumer who has received updates up to vscid i, its
		provider validator set must be equal to the set on the provider
		when i was sent, mapped through the mapping at that time.
	*/
	validatorSetReplication := func() {

		// Get the provider set - at the corresponding time.
		pSet := d.providerValsets[d.lastTimeConsumer]
		// Get the consumer set.
		cSet := d.consumerValset

		// Check that the two validator sets match exactly.
		require.Equal(d.t, len(pSet), len(cSet))

		for _, u := range pSet {

			// Find the appropriate forward mapping
			pk := u.PubKey
			expectedPower := u.Power
			found := false
			ck := keeper.ConsumerPubKey{}
			for k, v := range d.mappings[d.lastTimeConsumer] {
				if pk.Equal(k) {
					ck = v
				}
			}
			require.NotEqualf(d.t, ck, keeper.ConsumerPubKey{}, "bad test, a mapping must exist")

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
		For any key that the consumer is aware of, because it has
		received that key at some time in the past, and has not yet
		returned the maturity vscid for its removal:
		the key is useable as a query parameter to lookup the key
		of the validator which should be slashed for misbehavior.
	*/
	queries := func() {
		// For each key known to the consumer
		for _, u := range d.consumerValset {
			ckOnConsumer := u.PubKey

			// The query must return a result
			pkQueried, found := d.km.GetProviderPubKeyFromConsumerPubKey(ckOnConsumer)
			require.True(d.t, found)
			pkQueriedByConsAddr, found := d.km.GetProviderPubKeyFromConsumerConsAddress(keeper.ConsumerPubKeyToConsumerConsAddr(ckOnConsumer))
			require.True(d.t, found)
			require.Equal(d.t, pkQueried, pkQueriedByConsAddr)

			// The provider key must be the one that was actually referenced
			// in the latest trueMapping used to compute updates sent to the
			// consumer.
			ckWasActuallyMappedTo := map[keeper.ConsumerPubKey]bool{}
			actualMapping := d.mappings[d.lastTimeConsumer]
			for pk, ck := range actualMapping {

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
			require.Truef(d.t, good, "no mapping found for consumer key")
		}
	}

	/*
		All keys that the consumer definitely cannot use as a parameter in
		a slash request must eventually be pruned from state.
		A consumer can still reference a key if the last abci.ValidatorUpdate it received
		for the key had a positive power associated to it, OR the last abci.ValidatorUpdate
		had a 0 power associated (deletion) but the maturity period for that
		abci.ValidatorUpdate has not yet elapsed (and the maturity was not yet received
		on the provider chain).
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
				//    key should not be queryable unless it was used in a subsquent
				//    abci.ValidatorUpdate (see next block).
				expectQueryable[keeper.DeterministicStringify(u.PubKey)] = 0 < u.Power
			}
		}
		for i := d.lastTimeMaturity + 1; i <= d.lastTimeProvider; i++ {
			for _, u := range d.consumerUpdates[i] {
				// If a positive OR zero power abci.ValidatorUpdate was RECENTLY received
				// for the consumer, then the key must be queryable.
				expectQueryable[keeper.DeterministicStringify(u.PubKey)] = true
			}
		}
		// If a consumer key is CURRENTLY mapped to by a provider key, it
		// must be queryable.
		d.km.Store.IteratePkToCk(func(_, ck keeper.ConsumerPubKey) bool {
			expectQueryable[keeper.DeterministicStringify(ck)] = true
			return false
		})

		// Simply check every consumer key for the correct queryable-ness.
		for ck := uint64(0); ck < NUM_CKS; ck++ {
			ck += 100 //TODO: fix with others
			pk, actualQueryable := d.km.GetProviderPubKeyFromConsumerPubKey(key(ck))
			cca := keeper.ConsumerPubKeyToConsumerConsAddr(key(ck))
			pkByConsAddr, actualQueryableByConsAddr := d.km.GetProviderPubKeyFromConsumerConsAddress(cca)
			require.Equal(d.t, pk, pkByConsAddr)
			require.Equal(d.t, actualQueryable, actualQueryableByConsAddr)
			if expect, found := expectQueryable[keeper.DeterministicStringify(key(ck))]; found && expect {
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

	keyMappings := func() []keyMapEntry {
		ret := []keyMapEntry{}

		const NUM_ITS = 2 // Chosen arbitrarily/heuristically
		// Do this NUM_ITS times, to be able to generate conflicting mappings.
		// This is allowed by the KeyDel API, so it must be tested.
		for i := 0; i < NUM_ITS; i++ {
			// include none (to) all validators
			pks := rand.Perm(NUM_VALS)[0:rand.Intn(NUM_VALS+1)]
			for _, pk := range pks {
				ck := rand.Intn(NUM_CKS) + 100 // differentiate from pk
				ret = append(ret, keyMapEntry{key(uint64(pk)), key(uint64(ck))})
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
			ret = append(ret, abci.ValidatorUpdate{PubKey: key(uint64(pk)), Power: power})
		}
		return ret
	}

	// Get an initial key mapping.
	// The real system may use some manual set defaults.
	initialMappings := []keyMapEntry{}
	for pk := 0; pk < NUM_VALS; pk++ {
		ck := pk + 100 // differentiate from i
		initialMappings = append(initialMappings, keyMapEntry{key(uint64(pk)), key(uint64(ck))})
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

// go test -coverprofile=coverage.out -coverpkg=./... -timeout 1000m -run KeyMapPropertiesRandomlyHeuristically keymap_test.go

// Execute randomly generated traces (lists of actions)
// against new instances of the class, checking properties
// after each action is done.
func TestKeyMapPropertiesRandomlyHeuristically(t *testing.T) {
	for i := 0; i < NUM_TRACES; i++ {
		trace := []traceStep{}
		for len(trace) < 2 {
			trace = getTrace(t)
		}
		d := makeDriver(t, trace)
		d.run()
	}
}

func TestKeyMapKeySerialization(t *testing.T) {
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

func TestKeyMapMemo(t *testing.T) {
	arr := []ccvtypes.LastUpdateMemo{
		{}, {},
	}
	{
		k0 := key(0)
		k1 := key(1)
		arr[0].Pk = &k0
		arr[1].Pk = &k1
	}
	k2 := key(2)
	pk := &k2
	for i, m := range arr {
		if i < 1 {
			pk = m.Pk
		}
	}
	require.True(t, pk.Equal(key(0)))
}

func TestKeyMapMemoLoopIteration(t *testing.T) {
	m := ccvtypes.LastUpdateMemo{}
	{
		k0 := key(0)
		m.Pk = &k0
	}
	arr := []crypto.PublicKey{key(0), key(1)}
	for i, pk := range arr {
		if i < 1 {
			m.Pk = &pk
		}
	}
	require.False(t, m.Pk.Equal(arr[0]))
	require.True(t, m.Pk.Equal(arr[1]))
}

func TestKeyMapSameSeedEquality(t *testing.T) {
	k0 := key(0)
	k1 := key(0)
	require.True(t, k0.Equal(k1))
	require.Equal(t, k0, k1)
}

func TestKeyMapSameSeedMapLength(t *testing.T) {
	k0 := key(0)
	k1 := key(0)
	m := map[crypto.PublicKey]bool{}
	m[k0] = true
	m[k1] = true
	require.Equal(t, k0, k1)
	require.Len(t, m, 2)
}

func TestKeyMapSameSeedMapLengthCopy(t *testing.T) {
	k0 := key(0)
	arr := []crypto.PublicKey{k0}
	m := map[crypto.PublicKey]bool{}
	m[k0] = true
	m[arr[0]] = true
	require.Equal(t, k0, arr[0])
	require.Len(t, m, 1)
}

func TestKeyMapDifferentKeyComparison(t *testing.T) {
	k := key(0)
	bz, err := k.Marshal()
	require.Nil(t, err)
	other := crypto.PublicKey{}
	other.Unmarshal(bz)
	require.Equal(t, k, other)
	require.True(t, k.Equal(other))
	// No == comparison allowed!
	require.False(t, k == other)
	require.True(t, k != other)
}

func TestKeyMapSetCurrentQueryWithIdenticalKey(t *testing.T) {
	km := newTestKeyMap(t)
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	actual, _ := km.GetCurrentConsumerPubKeyFromProviderPubKey(key(42)) // Queryable
	require.Equal(t, key(43), actual)
}

func TestKeyMapSetCurrentQueryWithEqualKey(t *testing.T) {
	km := newTestKeyMap(t)
	k := key(42)
	km.SetProviderPubKeyToConsumerPubKey(k, key(43))

	kbz, err := k.Marshal()
	require.Nil(t, err)
	kEqual := crypto.PublicKey{}
	err = kEqual.Unmarshal(kbz)
	require.Nil(t, err)

	actual, _ := km.GetCurrentConsumerPubKeyFromProviderPubKey(kEqual) // Queryable
	require.Equal(t, key(43), actual)
}

func TestKeyMapNoSetReverseQuery(t *testing.T) {
	km := newTestKeyMap(t)
	_, found := km.GetProviderPubKeyFromConsumerPubKey(key(43)) // Not queryable
	require.False(t, found)
}

func TestKeyMapSetReverseQuery(t *testing.T) {
	km := newTestKeyMap(t)
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	actual, _ := km.GetProviderPubKeyFromConsumerPubKey(key(43)) // Queryable
	require.Equal(t, key(42), actual)
}

func TestKeyMapSetUseReplaceAndReverse(t *testing.T) {
	km := newTestKeyMap(t)
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	updates := []abci.ValidatorUpdate{{PubKey: key(42), Power: 999}}
	km.ComputeUpdates(100, updates)
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(44))       // New consumer key
	actual, _ := km.GetProviderPubKeyFromConsumerPubKey(key(43)) // Old is queryable
	require.Equal(t, key(42), actual)
	actual, _ = km.GetProviderPubKeyFromConsumerPubKey(key(44)) // New is queryable
	require.Equal(t, key(42), actual)
	km.ComputeUpdates(101, updates)                             // Old is garbage collected on consumer
	km.PruneUnusedKeys(102)                                     // Old is garbage collected on provider
	_, found := km.GetProviderPubKeyFromConsumerPubKey(key(43)) // Not queryable
	require.False(t, found)
	actual, _ = km.GetProviderPubKeyFromConsumerPubKey(key(44)) // New key is still queryable
	require.Equal(t, key(42), actual)
}

func TestKeyMapSetUseReplaceAndPrune(t *testing.T) {
	km := newTestKeyMap(t)
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	updates := []abci.ValidatorUpdate{{PubKey: key(42), Power: 999}}
	km.ComputeUpdates(100, updates)
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(44))
	actual, _ := km.GetProviderPubKeyFromConsumerPubKey(key(43)) // Queryable
	require.Equal(t, key(42), actual)
	actual, _ = km.GetProviderPubKeyFromConsumerPubKey(key(44)) // Queryable
	require.Equal(t, key(42), actual)
	km.PruneUnusedKeys(101)                                     // Should not be pruned
	_, found := km.GetProviderPubKeyFromConsumerPubKey(key(43)) // Still queryable
	require.True(t, found)
	actual, _ = km.GetProviderPubKeyFromConsumerPubKey(key(44)) // New key is still queryable
	require.Equal(t, key(42), actual)
}

func TestKeyMapSetUnsetReverseQuery(t *testing.T) {
	km := newTestKeyMap(t)
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(44))      // Set to different value
	_, found := km.GetProviderPubKeyFromConsumerPubKey(key(43)) // Ealier value not queryable
	require.False(t, found)
}

func TestKeyMapGCUpdateIsEmitted(t *testing.T) {
	km := newTestKeyMap(t)
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(43))
	updates := []abci.ValidatorUpdate{{PubKey: key(42), Power: 999}}
	km.ComputeUpdates(100, updates)
	km.SetProviderPubKeyToConsumerPubKey(key(42), key(44)) // Now use a different consumer key
	consumerUpdates := km.ComputeUpdates(100, []abci.ValidatorUpdate{})
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

func compareForEquality(t *testing.T,
	km keeper.KeyMap,
	pkToCk map[keeper.ProviderPubKey]keeper.ConsumerPubKey,
	ckToPk map[keeper.ConsumerPubKey]keeper.ProviderPubKey,
	ckToMemo map[string]ccvtypes.LastUpdateMemo) {

	cnt := 0
	km.Store.IteratePkToCk(func(_, _ keeper.ConsumerPubKey) bool {
		cnt += 1
		return false
	})
	require.Equal(t, len(pkToCk), cnt)

	cnt = 0
	km.Store.IterateCkToPk(func(_, _ keeper.ConsumerPubKey) bool {
		cnt += 1
		return false
	})
	require.Equal(t, len(ckToPk), cnt)

	cnt = 0
	km.Store.IterateCkToMemo(func(_ keeper.ConsumerConsAddr, _ ccvtypes.LastUpdateMemo) bool {
		cnt += 1
		return false
	})
	require.Equal(t, len(ckToMemo), cnt)

	for k, vExpect := range pkToCk {
		vActual, found := km.Store.GetPkToCk(k)
		require.True(t, found)
		require.Equal(t, vExpect, vActual)
	}
	for k, vExpect := range ckToPk {
		vActual, found := km.Store.GetCkToPk(k)
		require.True(t, found)
		require.Equal(t, vExpect, vActual)
	}
	for k, vExpect := range ckToMemo {
		k := sdk.ConsAddress(k)
		m, found := km.Store.GetCkToMemo(k)
		require.True(t, found)
		require.Equal(t, vExpect.Pk, m.Pk)
		require.Equal(t, vExpect.Ck, m.Ck)
		require.Equal(t, vExpect.Vscid, m.Vscid)
		require.Equal(t, vExpect.Power, m.Power)
	}

}

func checkCorrectSerializationAndDeserialization(t *testing.T,
	chainID string, keys []crypto.PublicKey,
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

	pkToCk := map[keeper.ProviderPubKey]keeper.ConsumerPubKey{}
	ckToPk := map[keeper.ConsumerPubKey]keeper.ProviderPubKey{}
	ckToMemo := map[string]ccvtypes.LastUpdateMemo{}

	pkToCk[keys[0]] = keys[1]
	pkToCk[keys[2]] = keys[3]
	ckToPk[keys[4]] = keys[5]
	ckToPk[keys[6]] = keys[7]
	ckToMemo[string(keeper.ConsumerPubKeyToConsumerConsAddr(keys[8]))] = ccvtypes.LastUpdateMemo{
		Ck:    &keys[9],
		Pk:    &keys[10],
		Vscid: uint64_0,
		Power: int64_0,
	}
	ckToMemo[string(keeper.ConsumerPubKeyToConsumerConsAddr(keys[11]))] = ccvtypes.LastUpdateMemo{
		Ck:    &keys[12],
		Pk:    &keys[13],
		Vscid: uint64_1,
		Power: int64_1,
	}

	{
		// Use one KeyMap instance to serialize the data
		store := keeper.KeyMapStore{keeperParams.Ctx.KVStore(keeperParams.StoreKey), chainID}
		km := keeper.MakeKeyMap(&store)
		for k, v := range pkToCk {
			km.Store.SetPkToCk(k, v)
		}
		for k, v := range ckToPk {
			km.Store.SetCkToPk(k, v)
		}
		for k, v := range ckToMemo {
			km.Store.SetCkToMemo(sdk.ConsAddress(k), v)
		}
	}

	// Use another KeyMap instance to deserialize the data
	store := keeper.KeyMapStore{keeperParams.Ctx.KVStore(keeperParams.StoreKey), chainID}
	km := keeper.MakeKeyMap(&store)

	// Check that the data is the same

	compareForEquality(t, km, pkToCk, ckToPk, ckToMemo)
}

func TestKeyMapSerializationAndDeserialization(t *testing.T) {
	keys := []crypto.PublicKey{}
	for i := uint64(0); i < 16; i++ {
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
