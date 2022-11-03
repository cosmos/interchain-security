package keeper_test

import (
	"fmt"
	"math/rand"
	"testing"
	"time"

	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/tendermint/crypto/ed25519"
	tmtypes "github.com/tendermint/tendermint/types"
	"golang.org/x/exp/slices"
)

// Tests the edge case behavior where duplicate slash packet entires are queued in the same block.
func TestDupSlashPackets(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	ctx = ctx.WithBlockTime(time.Now())

	entry := providertypes.NewSlashPacketEntry(ctx.BlockTime(), "chain-7", ed25519.GenPrivKey().PubKey().Address())

	providerKeeper.QueuePendingSlashPacketEntry(ctx, entry)

	entries := providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 1, len(entries))
	require.Equal(t, entries[0], entry)

	// Queue new in-mem object with same data
	newButDupEntry := providertypes.NewSlashPacketEntry(ctx.BlockTime(), "chain-7", entry.ValAddr)
	providerKeeper.QueuePendingSlashPacketEntry(ctx, newButDupEntry)

	// Duplicate entry should overwrite the old one with the same data, so length should still be 1
	entries = providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 1, len(entries))
	require.Equal(t, entries[0], entry)

	// Prove that a non duplicate entry doesn't overwrite the existing entry
	nonDupEntry := providertypes.NewSlashPacketEntry(ctx.BlockTime(), "chain-8", entry.ValAddr)
	providerKeeper.QueuePendingSlashPacketEntry(ctx, nonDupEntry)

	entries = providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 2, len(entries))
	require.Equal(t, entries[0], entry)
	require.Equal(t, entries[1], nonDupEntry)
}

// TestPendingSlashPacket tests the queue and iteration functions for pending slash packet entries,
// with assertion of FIFO ordering
func TestPendingSlashPacketEntries(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Consistent time for "now"
	now := time.Now()

	entries := providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 0, len(entries))

	// Queue 3 entries for chainIDs 0, 1, 2
	for i := 0; i < 3; i++ {
		entry := providertypes.NewSlashPacketEntry(now,
			fmt.Sprintf("chain-%d", i), ed25519.GenPrivKey().PubKey().Address())
		providerKeeper.QueuePendingSlashPacketEntry(ctx, entry)
	}
	entries = providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 3, len(entries))

	// Queue 3 entries for chainIDs 0, 1, 2 an hour later
	for i := 0; i < 3; i++ {
		entry := providertypes.NewSlashPacketEntry(now.Add(time.Hour),
			fmt.Sprintf("chain-%d", i), ed25519.GenPrivKey().PubKey().Address())
		providerKeeper.QueuePendingSlashPacketEntry(ctx, entry)
	}

	// Retrieve entries from store
	entries = providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 6, len(entries))

	// Assert that entries are obtained in FIFO order according to block time
	firstChainIdSet := []string{entries[0].ConsumerChainID, entries[1].ConsumerChainID, entries[2].ConsumerChainID}
	require.True(t, slices.Contains(firstChainIdSet, "chain-0"))
	require.True(t, slices.Contains(firstChainIdSet, "chain-1"))
	require.True(t, slices.Contains(firstChainIdSet, "chain-2"))
	secondChainIdSet := []string{entries[3].ConsumerChainID, entries[4].ConsumerChainID, entries[5].ConsumerChainID}
	require.True(t, slices.Contains(secondChainIdSet, "chain-0"))
	require.True(t, slices.Contains(secondChainIdSet, "chain-1"))
	require.True(t, slices.Contains(secondChainIdSet, "chain-2"))

	// Queue 3 entries for chainIDs 5, 6, 7 another hour later
	for i := 0; i < 3; i++ {
		entry := providertypes.NewSlashPacketEntry(now.Add(2*time.Hour),
			fmt.Sprintf("chain-%d", i+5), ed25519.GenPrivKey().PubKey().Address())
		providerKeeper.QueuePendingSlashPacketEntry(ctx, entry)
	}

	// Retrieve entries from store
	entries = providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 9, len(entries))

	// Assert that entries are obtained in FIFO order according to block time
	firstChainIdSet = []string{entries[0].ConsumerChainID, entries[1].ConsumerChainID, entries[2].ConsumerChainID}
	require.True(t, slices.Contains(firstChainIdSet, "chain-0"))
	require.True(t, slices.Contains(firstChainIdSet, "chain-1"))
	require.True(t, slices.Contains(firstChainIdSet, "chain-2"))
	secondChainIdSet = []string{entries[3].ConsumerChainID, entries[4].ConsumerChainID, entries[5].ConsumerChainID}
	require.True(t, slices.Contains(secondChainIdSet, "chain-0"))
	require.True(t, slices.Contains(secondChainIdSet, "chain-1"))
	require.True(t, slices.Contains(secondChainIdSet, "chain-2"))
	thirdChainIdSet := []string{entries[6].ConsumerChainID, entries[7].ConsumerChainID, entries[8].ConsumerChainID}
	require.True(t, slices.Contains(thirdChainIdSet, "chain-5"))
	require.True(t, slices.Contains(thirdChainIdSet, "chain-6"))
	require.True(t, slices.Contains(thirdChainIdSet, "chain-7"))

	// Test the callback break functionality of the iterator
	entries = []providertypes.SlashPacketEntry{}
	providerKeeper.IteratePendingSlashPacketEntries(ctx, func(entry providertypes.SlashPacketEntry) bool {
		entries = append(entries, entry)
		// Break after any of the third set of entry is seen
		return slices.Contains(thirdChainIdSet, entry.ConsumerChainID)
	})
	// Expect first two sets of entries to be seen, and one packet from the third set
	require.Equal(t, 7, len(entries))
}

// TestPendingSlashPacketEntryDeletion tests the deletion function for
// pending slash packet entries with assertion of FIFO ordering.
func TestPendingSlashPacketEntryDeletion(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := time.Now()

	entries := providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 0, len(entries))

	// Instantiate entries in the expected order we wish to get them back as (ordered by recv time)
	entries = []providertypes.SlashPacketEntry{}
	entries = append(entries, providertypes.NewSlashPacketEntry(now, "chain-0", ed25519.GenPrivKey().PubKey().Address()))
	entries = append(entries, providertypes.NewSlashPacketEntry(now.Add(time.Hour).UTC(), "chain-1", ed25519.GenPrivKey().PubKey().Address()))
	entries = append(entries, providertypes.NewSlashPacketEntry(now.Add(2*time.Hour).Local(), "chain-2", ed25519.GenPrivKey().PubKey().Address()))
	entries = append(entries, providertypes.NewSlashPacketEntry(now.Add(3*time.Hour).In(time.FixedZone("UTC-8", -8*60*60)), "chain-3", ed25519.GenPrivKey().PubKey().Address()))
	entries = append(entries, providertypes.NewSlashPacketEntry(now.Add(4*time.Hour).Local(), "chain-4", ed25519.GenPrivKey().PubKey().Address()))
	entries = append(entries, providertypes.NewSlashPacketEntry(now.Add(5*time.Hour).UTC(), "chain-5", ed25519.GenPrivKey().PubKey().Address()))
	entries = append(entries, providertypes.NewSlashPacketEntry(now.Add(6*time.Hour).Local(), "chain-6", ed25519.GenPrivKey().PubKey().Address()))

	// Instantiate shuffled copy of above slice
	shuffledEntries := append([]providertypes.SlashPacketEntry{}, entries...)
	rand.Seed(now.UnixNano())
	rand.Shuffle(len(shuffledEntries), func(i, j int) {
		shuffledEntries[i], shuffledEntries[j] = shuffledEntries[j], shuffledEntries[i]
	})

	// Queue 7 slash packets with various block times in random order
	for _, entry := range shuffledEntries {
		providerKeeper.QueuePendingSlashPacketEntry(ctx, entry)
	}

	gotEntries := providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 7, len(gotEntries))

	// Assert obtained order is decided upon via packet recvTime, not insertion order
	gotEntries = providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	for i, gotEntry := range gotEntries {
		expectedEntry := entries[i]
		require.Equal(t, expectedEntry, gotEntry)
	}

	// Confirm no mutations have occurred from test helper
	gotEntries = providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 7, len(gotEntries))

	// Delete packets 1, 3, 5 (0-indexed)
	providerKeeper.DeletePendingSlashPacketEntries(ctx, gotEntries[1], gotEntries[3], gotEntries[5])

	// Assert deletion and ordering
	gotEntries = providerKeeper.GetAllPendingSlashPacketEntries(ctx)
	require.Equal(t, 4, len(gotEntries))
	require.Equal(t, "chain-0", gotEntries[0].ConsumerChainID)
	// Packet 1 was deleted
	require.Equal(t, "chain-2", gotEntries[1].ConsumerChainID)
	// Packet 3 was deleted
	require.Equal(t, "chain-4", gotEntries[2].ConsumerChainID)
	// Packet 5 was deleted
	require.Equal(t, "chain-6", gotEntries[3].ConsumerChainID)
}

// Struct used for TestPendingPacketData and helpers
type pendingPacketDataInstance struct {
	IbcSeqNum uint64
	Data      interface{}
}

// getAllPendingPacketDataInstances returns all pending packet data instances in order from the pending packet data queue
func getAllPendingPacketDataInstances(k *keeper.Keeper, ctx sdktypes.Context, consumerChainId string) (instances []pendingPacketDataInstance) {
	k.IteratePendingPacketData(ctx, consumerChainId, func(ibcSeqNum uint64, data interface{}) bool {
		instances = append(instances, pendingPacketDataInstance{IbcSeqNum: ibcSeqNum, Data: data})
		return false
	})
	return
}

// getOrderedInstances returns the given instances in order, specified by the given indexes
func getOrderedInstances(instances []pendingPacketDataInstance, orderbyIdx []int) (orderedInstances []pendingPacketDataInstance) {
	toReturn := []pendingPacketDataInstance{}
	for _, idx := range orderbyIdx {
		toReturn = append(toReturn, instances[idx])
	}
	return toReturn
}

// Asserts that the pending packet data retrieved for this consumer chain matches what's expected
func assertPendingPacketDataOrdering(t *testing.T, k *keeper.Keeper, ctx sdktypes.Context,
	consumerChainId string, expectedInstances []pendingPacketDataInstance) {
	// Get all packet data for this chain
	obtainedInstances := getAllPendingPacketDataInstances(k, ctx, consumerChainId)
	// No extra data should be present
	require.Equal(t, len(expectedInstances), len(obtainedInstances))
	// Assert order and correct serialization/deserialization for each data instance
	for i, obtainedInstance := range obtainedInstances {
		require.Equal(t, expectedInstances[i], obtainedInstance)
	}
}

// TestPendingPacketData tests the pending packet data queuing, iteration and deletion functionality.
func TestPendingPacketData(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	packetDataForMultipleConsumers := []struct {
		chainID   string
		instances []pendingPacketDataInstance

		// Expected order of data instances after retrieval from store, before deletion (specified by instance index)
		expectedOrder []int
		// Data instances to delete (specified by instance index)
		toDelete []int
		// Expected order of data instances after deletion (specified by instance index)
		expectedOrderAfterDeletion []int
	}{
		// Note, duplicate ibc sequence numbers are not tested, as we assume ibc behaves correctly
		{
			chainID: "chain-0",
			instances: []pendingPacketDataInstance{
				{IbcSeqNum: 0, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 1, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 2, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 3, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 4, Data: testkeeper.GetNewSlashPacketData()},
			},
			expectedOrder:              []int{0, 1, 2, 3, 4},
			toDelete:                   []int{0, 2, 4},
			expectedOrderAfterDeletion: []int{1, 3},
		},
		{
			chainID: "chain-7",
			instances: []pendingPacketDataInstance{
				{IbcSeqNum: 96, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 78, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 12, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 0, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 1, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 78972, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 9999999999999999999, Data: testkeeper.GetNewSlashPacketData()},
			},
			expectedOrder:              []int{3, 4, 2, 1, 0, 5, 6},
			toDelete:                   []int{0, 1, 2, 3, 4, 5},
			expectedOrderAfterDeletion: []int{6},
		},
		{
			chainID: "chain-thats-not-0-or-7",
			instances: []pendingPacketDataInstance{
				{IbcSeqNum: 9, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 8, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 7, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 6, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 5, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 1, Data: testkeeper.GetNewVSCMaturedPacketData()},
			},
			expectedOrder:              []int{5, 4, 3, 2, 1, 0},
			toDelete:                   []int{1, 2, 3, 4, 5},
			expectedOrderAfterDeletion: []int{0},
		},
	}

	// Queue all packet data at once
	for _, chainData := range packetDataForMultipleConsumers {
		for _, dataInstance := range chainData.instances {
			// Queue each instance differently depending on type
			if slashData, ok := dataInstance.Data.(ccvtypes.SlashPacketData); ok {
				providerKeeper.QueuePendingSlashPacketData(ctx, chainData.chainID, dataInstance.IbcSeqNum, slashData)

			} else if vscMaturedData, ok := dataInstance.Data.(ccvtypes.VSCMaturedPacketData); ok {
				providerKeeper.QueuePendingVSCMaturedPacketData(ctx, chainData.chainID, dataInstance.IbcSeqNum, vscMaturedData)

			} else {
				panic("invalid data type")
			}
		}
	}

	// Assert retrieval ordering for each chain
	for _, chainData := range packetDataForMultipleConsumers {
		expectedInstances := getOrderedInstances(chainData.instances, chainData.expectedOrder)
		assertPendingPacketDataOrdering(t, &providerKeeper, ctx, chainData.chainID, expectedInstances)
	}

	// Delete specified data all at once
	for _, chainData := range packetDataForMultipleConsumers {
		for _, i := range chainData.toDelete {
			providerKeeper.DeletePendingPacketData(ctx, chainData.chainID, chainData.instances[i].IbcSeqNum)
		}
	}

	// Assert retrieval ordering after deletion for each chain
	for _, chainData := range packetDataForMultipleConsumers {
		expectedInstances := getOrderedInstances(chainData.instances, chainData.expectedOrderAfterDeletion)
		assertPendingPacketDataOrdering(t, &providerKeeper, ctx, chainData.chainID, expectedInstances)
	}
}

// TestSlashGasMeter tests the getter and setter for the slash gas meter
func TestSlashGasMeter(t *testing.T) {

	testCases := []struct {
		meterValue  sdk.Int
		shouldPanic bool
	}{
		{meterValue: sdk.NewInt(-7999999999999999999), shouldPanic: true},
		{meterValue: sdk.NewInt(-tmtypes.MaxTotalVotingPower - 1), shouldPanic: true},
		{meterValue: sdk.NewInt(-tmtypes.MaxTotalVotingPower), shouldPanic: false},
		{meterValue: sdk.NewInt(-50000000078987), shouldPanic: false},
		{meterValue: sdk.NewInt(-4237), shouldPanic: false},
		{meterValue: sdk.NewInt(0), shouldPanic: false},
		{meterValue: sdk.NewInt(1), shouldPanic: false},
		{meterValue: sdk.NewInt(4237897), shouldPanic: false},
		{meterValue: sdk.NewInt(500078078987), shouldPanic: false},
		{meterValue: sdk.NewInt(tmtypes.MaxTotalVotingPower), shouldPanic: false},
		{meterValue: sdk.NewInt(tmtypes.MaxTotalVotingPower + 1), shouldPanic: true},
		{meterValue: sdk.NewInt(7999974823991111199), shouldPanic: true},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		if tc.shouldPanic {
			require.Panics(t, func() {
				providerKeeper.SetSlashGasMeter(ctx, tc.meterValue)
			})
		} else {
			providerKeeper.SetSlashGasMeter(ctx, tc.meterValue)
			gotMeterValue := providerKeeper.GetSlashGasMeter(ctx)
			require.Equal(t, tc.meterValue, gotMeterValue)
		}
	}
}

// TestLastSlashGasReplenishTime tests the getter and setter for the last slash gas replenish time
func TestLastSlashGasReplenishTime(t *testing.T) {

	testCases := []time.Time{
		time.Now(),
		time.Now().Add(1 * time.Hour).UTC(),
		time.Now().Add(2 * time.Hour).Local(),
		time.Now().Add(3 * time.Hour).In(time.FixedZone("UTC-8", -8*60*60)),
		time.Now().Add(4 * time.Hour).Local(),
		time.Now().Add(-1 * time.Hour).UTC(),
		time.Now().Add(-2 * time.Hour).Local(),
		time.Now().Add(-3 * time.Hour).UTC(),
		time.Now().Add(-4 * time.Hour).Local(),
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		providerKeeper.SetLastSlashGasReplenishTime(ctx, tc)
		gotTime := providerKeeper.GetLastSlashGasReplenishTime(ctx)
		// Time should be returned in UTC
		require.Equal(t, tc.UTC(), gotTime)
	}
}
