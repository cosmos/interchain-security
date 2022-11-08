package keeper_test

import (
	"errors"
	"fmt"
	"math/rand"
	"testing"
	"time"

	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/tendermint/crypto/ed25519"
	tmtypes "github.com/tendermint/tendermint/types"
	"golang.org/x/exp/slices"
)

// TestHandlePacketDataForChain tests the HandlePacketDataForChain function. Note: Only one consumer is tested here,
// but multiple consumers are tested in TestPendingPacketData.
// TODO: will need to separately test that no vsc matured packet is queued without a slash packet already in the queue
// ^ make a corresponding test for the place that queues up that packet, gaurunteeing vsc matured will never be at the head.
func TestHandlePacketDataForChain(t *testing.T) {

	testCases := []struct {
		name    string
		chainID string
		// Pending packet data that will be queued in the order specified by the slice
		dataToQueue []interface{}
		// Indexes of packet data from dataToQueue that are expected to be handled and deleted from store
		expectedHandledIndexes []int
	}{
		{
			"no packets",
			"my-cool-chain",
			[]interface{}{},
			[]int{},
		},
		{
			"one slash packet should be handled",
			"chain-37",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
			},
			[]int{0},
		},
		{
			"one slash packet followed by one vsc matured packet should all be handled",
			"chain-222",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
			},
			[]int{0, 1},
		},
		{
			"one slash packet followed by multiple vsc matured packets should all be handled",
			"chain-2223",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
			},
			[]int{0, 1, 2, 3, 4, 5},
		},
		{
			"multiple slash packets followed by multiple vsc matured packets should only handle first slash packet",
			"chain-9",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
			},
			[]int{0},
		},
		{
			"vsc matured packets sandwiched between slash packets should handle everything but the last slash packet",
			"chain-000",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(), // 10th index not included in expectedHandledIndexes
			},
			[]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
		},
		{
			"alternating slash and vsc matured packets should handle only the first slash, and trailing vsc matured packets",
			"chain-00000",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
			},
			[]int{0, 1, 2},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		// Queue pending packet data, where chainID is arbitrary, and ibc seq number is index of the data instance
		for i, data := range tc.dataToQueue {
			queuePendingPacketData(ctx, &providerKeeper, tc.chainID, uint64(i), data)
		}

		// Define our handler callbacks to simply store the data instances that are handled
		handledData := []interface{}{}
		slashHandleCounter := func(ctx sdktypes.Context, chainID string, data ccvtypes.SlashPacketData) (bool, error) {
			handledData = append(handledData, data)
			return true, nil
		}
		vscMaturedHandleCounter := func(ctx sdktypes.Context, chainID string, data ccvtypes.VSCMaturedPacketData) {
			handledData = append(handledData, data)
		}

		providerKeeper.HandlePacketDataForChain(ctx, tc.chainID, slashHandleCounter, vscMaturedHandleCounter)

		// Assert number of handled data instances matches expected number
		require.Equal(t, len(tc.expectedHandledIndexes), len(handledData))

		// Assert handled data instances match expected value
		for i, expectedIndex := range tc.expectedHandledIndexes {
			require.Equal(t, tc.dataToQueue[expectedIndex], handledData[i])
		}

		// Sanity check, Assert that only the first handled packet is a slash packet, and the rest are vsc matured packets
		for idx, instance := range handledData {
			switch instance.(type) {
			case ccvtypes.SlashPacketData:
				require.Equal(t, 0, idx)
			case ccvtypes.VSCMaturedPacketData:
			default:
				require.Fail(t, "unexpected data instance type")
			}
		}

		// Assert that the unhandled queued data instances are as expected (i.e no unexpected deletions)
		expectedDataThatsLeft := []interface{}{}
		for idx, data := range tc.dataToQueue {
			if !slices.Contains(tc.expectedHandledIndexes, idx) {
				expectedDataThatsLeft = append(expectedDataThatsLeft, data)
			}
		}

		dataThatsLeft := []interface{}{}
		providerKeeper.IteratePendingPacketData(ctx, tc.chainID, func(ibcSeqNum uint64, data interface{}) bool {
			dataThatsLeft = append(dataThatsLeft, data)
			return false
		})

		require.Equal(t, expectedDataThatsLeft, dataThatsLeft)

		// Assert that each instance of handled data is deleted from the persisted queue (i.e deletions where expected)
		for _, dataInstance := range handledData {
			require.NotContains(t, dataThatsLeft, dataInstance)
		}
	}
}

// TestHandlePacketDataForChainPanic tests that HandlePacketDataForChain panics when expected
func TestHandlePacketDataForChainPanic(t *testing.T) {
	testCases := []struct {
		name         string
		dataToQueue  []interface{}
		slashHandler func(ctx sdktypes.Context, chainID string, data ccvtypes.SlashPacketData) (bool, error)
	}{
		{
			"panic when slash packet data is not first in queue",
			[]interface{}{
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(),
			},
			func(ctx sdktypes.Context, chainID string, data ccvtypes.SlashPacketData) (bool, error) {
				return true, nil
			},
		},
		// Panic for invalid persisted data is skipped, its not worth adding a keeper method to allow for invalid data
		{
			"panic when slash handler returns error",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
			},
			func(ctx sdktypes.Context, chainID string,
				data ccvtypes.SlashPacketData) (bool, error) {
				return false, errors.New("error")
			},
		},
	}
	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		for i, data := range tc.dataToQueue {
			queuePendingPacketData(ctx, &providerKeeper, "chainID", uint64(i), data)
		}

		require.Panics(t, func() {
			providerKeeper.HandlePacketDataForChain(ctx, "chainID", tc.slashHandler, func(ctx sdktypes.Context, chainID string, data ccvtypes.VSCMaturedPacketData) {})
		})
	}
}

// TODO: test for CheckForSlashMeterReplenishment. This could prob use a unit and e2e test

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
			queuePendingPacketData(ctx, &providerKeeper, chainData.chainID, dataInstance.IbcSeqNum, dataInstance.Data)
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

// TestPanicIfTooMuchPendingPacketData tests the PanicIfTooMuchPendingPacketData method.
func TestPanicIfTooMuchPendingPacketData(t *testing.T) {

	// todo: set param to max and test more cases
	testCases := []struct {
		max uint64
	}{
		{max: 15},
	}

	for _, tc := range testCases {

		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()
		rand.Seed(time.Now().UnixNano())

		// Queue packet data instances until we reach the max (some slash packets, some VSC matured packets)
		reachedMax := false
		for i := 0; i < int(tc.max+2); i++ { // iterate up to tc.max+1
			randBool := rand.Intn(2) == 0
			var data interface{}
			if randBool {
				data = testkeeper.GetNewSlashPacketData()
			} else {
				data = testkeeper.GetNewVSCMaturedPacketData()
			}
			// Panic only if we've reached the max
			if i == int(tc.max+1) {
				require.Panics(t, func() {
					queuePendingPacketData(ctx, &providerKeeper, "chain-0", uint64(i), data)
				})
				reachedMax = true
			} else {
				queuePendingPacketData(ctx, &providerKeeper, "chain-0", uint64(i), data)
			}
		}
		require.True(t, reachedMax)
	}
}

// TestPendingPacketDataSize tests the getter, setter and incrementer for pending packet data size.
func TestPendingPacketDataSize(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Confirm initial size is 0
	require.Equal(t, uint64(0), providerKeeper.GetPendingPacketDataSize(ctx, "chain-0"))

	// Set pending packet data size and confirm it was set
	providerKeeper.SetPendingPacketDataSize(ctx, "chain-0", 10)
	require.Equal(t, uint64(10), providerKeeper.GetPendingPacketDataSize(ctx, "chain-0"))

	// Increment pending packet data size and confirm it was incremented
	providerKeeper.IncrementPendingPacketDataSize(ctx, "chain-0")
	require.Equal(t, uint64(11), providerKeeper.GetPendingPacketDataSize(ctx, "chain-0"))
}

// TestSlashMeter tests the getter and setter for the slash gas meter
func TestSlashMeter(t *testing.T) {

	testCases := []struct {
		meterValue  sdktypes.Int
		shouldPanic bool
	}{
		{meterValue: sdktypes.NewInt(-7999999999999999999), shouldPanic: true},
		{meterValue: sdktypes.NewInt(-tmtypes.MaxTotalVotingPower - 1), shouldPanic: true},
		{meterValue: sdktypes.NewInt(-tmtypes.MaxTotalVotingPower), shouldPanic: false},
		{meterValue: sdktypes.NewInt(-50000000078987), shouldPanic: false},
		{meterValue: sdktypes.NewInt(-4237), shouldPanic: false},
		{meterValue: sdktypes.NewInt(0), shouldPanic: false},
		{meterValue: sdktypes.NewInt(1), shouldPanic: false},
		{meterValue: sdktypes.NewInt(4237897), shouldPanic: false},
		{meterValue: sdktypes.NewInt(500078078987), shouldPanic: false},
		{meterValue: sdktypes.NewInt(tmtypes.MaxTotalVotingPower), shouldPanic: false},
		{meterValue: sdktypes.NewInt(tmtypes.MaxTotalVotingPower + 1), shouldPanic: true},
		{meterValue: sdktypes.NewInt(7999974823991111199), shouldPanic: true},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		if tc.shouldPanic {
			require.Panics(t, func() {
				providerKeeper.SetSlashMeter(ctx, tc.meterValue)
			})
		} else {
			providerKeeper.SetSlashMeter(ctx, tc.meterValue)
			gotMeterValue := providerKeeper.GetSlashMeter(ctx)
			require.Equal(t, tc.meterValue, gotMeterValue)
		}
	}
}

// TestLastSlashMeterReplenishTime tests the getter and setter for the last slash meter replenish time
func TestLastSlashMeterReplenishTime(t *testing.T) {

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

		providerKeeper.SetLastSlashMeterReplenishTime(ctx, tc)
		gotTime := providerKeeper.GetLastSlashMeterReplenishTime(ctx)
		// Time should be returned in UTC
		require.Equal(t, tc.UTC(), gotTime)
	}
}

// Struct used for TestPendingPacketData and helpers
type pendingPacketDataInstance struct {
	IbcSeqNum uint64
	Data      interface{}
}

// queuePendingPacketData queues the given pending packet data as it's appropriate concrete type
func queuePendingPacketData(ctx sdktypes.Context, k *keeper.Keeper, chainID string, ibcSeqNum uint64, data interface{}) {
	// Queue data differently depending on concrete type
	if slashData, ok := data.(ccvtypes.SlashPacketData); ok {
		k.QueuePendingSlashPacketData(ctx, chainID, ibcSeqNum, slashData)

	} else if vscMaturedData, ok := data.(ccvtypes.VSCMaturedPacketData); ok {
		k.QueuePendingVSCMaturedPacketData(ctx, chainID, ibcSeqNum, vscMaturedData)

	} else {
		panic("invalid data type")
	}
}

// getAllPendingPacketDataInstances returns all pending packet data instances in order from the pending packet data queue
func getAllPendingPacketDataInstances(ctx sdktypes.Context, k *keeper.Keeper, consumerChainId string) (instances []pendingPacketDataInstance) {
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
	obtainedInstances := getAllPendingPacketDataInstances(ctx, k, consumerChainId)
	// No extra data should be present
	require.Equal(t, len(expectedInstances), len(obtainedInstances))
	// Assert order and correct serialization/deserialization for each data instance
	for i, obtainedInstance := range obtainedInstances {
		require.Equal(t, expectedInstances[i], obtainedInstance)
	}
}
