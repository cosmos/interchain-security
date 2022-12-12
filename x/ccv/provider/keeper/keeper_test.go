package keeper_test

import (
	"fmt"
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"

	ibcsimapp "github.com/cosmos/ibc-go/v3/testing/simapp"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"

	"github.com/stretchr/testify/require"
)

// TestValsetUpdateBlockHeight tests the getter, setter, and deletion methods for valset updates mapped to block height
func TestValsetUpdateBlockHeight(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	testCases := []struct {
		vscID         uint64
		height        uint64
		iteratorIndex int
	}{
		{vscID: 2, height: 22, iteratorIndex: 1},
		{vscID: 1, height: 11, iteratorIndex: 0},
		{vscID: 3, height: 33, iteratorIndex: 2},
	}

	found := false
	providerKeeper.IterateAllValsetUpdateBlockHeight(ctx, func(vscID, height uint64) {
		found = true
	})
	require.False(t, found)

	for _, tc := range testCases {
		providerKeeper.SetValsetUpdateBlockHeight(ctx, tc.vscID, tc.height)
	}

	for _, tc := range testCases {
		height, found := providerKeeper.GetValsetUpdateBlockHeight(ctx, tc.vscID)
		require.True(t, found)
		require.Equal(t, tc.height, height)
	}

	heights := []uint64{}
	providerKeeper.IterateAllValsetUpdateBlockHeight(ctx, func(_, height uint64) {
		heights = append(heights, height)
	})
	require.Len(t, heights, len(testCases))
	for _, tc := range testCases {
		require.Equal(t, tc.height, heights[tc.iteratorIndex])
	}

	providerKeeper.DeleteValsetUpdateBlockHeight(ctx, testCases[0].vscID)
	_, found = providerKeeper.GetValsetUpdateBlockHeight(ctx, testCases[0].vscID)
	require.False(t, found)
}

// TestSlashAcks tests the getter, setter, iteration, and deletion methods for stored slash acknowledgements
func TestSlashAcks(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	var chainsAcks [][]string

	penaltiesfN := func() (penalties []string) {
		providerKeeper.IterateAllSlashAcks(ctx, func(id string, acks []string) {
			chainsAcks = append(chainsAcks, acks)
		})
		return
	}

	chainID := "consumer"

	acks := providerKeeper.GetSlashAcks(ctx, chainID)
	require.Nil(t, acks)

	p := []string{"alice", "bob", "charlie"}
	providerKeeper.SetSlashAcks(ctx, chainID, p)

	acks = providerKeeper.GetSlashAcks(ctx, chainID)
	require.NotNil(t, acks)

	require.Len(t, acks, 3)
	slashAcks := providerKeeper.ConsumeSlashAcks(ctx, chainID)
	require.Len(t, slashAcks, 3)

	acks = providerKeeper.GetSlashAcks(ctx, chainID)
	require.Nil(t, acks)

	chains := []string{"c1", "c2", "c3"}

	for _, c := range chains {
		providerKeeper.SetSlashAcks(ctx, c, p)
	}

	penaltiesfN()
	require.Len(t, chainsAcks, len(chains))
}

// TestAppendSlashAck tests the append method for stored slash acknowledgements
func TestAppendSlashAck(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	p := []string{"alice", "bob", "charlie"}
	chains := []string{"c1", "c2"}
	providerKeeper.SetSlashAcks(ctx, chains[0], p)

	providerKeeper.AppendSlashAck(ctx, chains[0], p[0])
	acks := providerKeeper.GetSlashAcks(ctx, chains[0])
	require.NotNil(t, acks)
	require.Len(t, acks, len(p)+1)

	providerKeeper.AppendSlashAck(ctx, chains[1], p[0])
	acks = providerKeeper.GetSlashAcks(ctx, chains[1])
	require.NotNil(t, acks)
	require.Len(t, acks, 1)
}

// TestPendingVSCs tests the getter, appending, and deletion methods for stored pending VSCs
func TestPendingVSCs(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "consumer"

	pending := providerKeeper.GetPendingPackets(ctx, chainID)
	require.Len(t, pending, 0)

	pks := ibcsimapp.CreateTestPubKeys(4)
	var ppks [4]tmprotocrypto.PublicKey
	for i, pk := range pks {
		ppks[i], _ = cryptocodec.ToTmProtoPublicKey(pk)
	}

	packetList := []ccv.ValidatorSetChangePacketData{
		{
			ValidatorUpdates: []abci.ValidatorUpdate{
				{PubKey: ppks[0], Power: 1},
				{PubKey: ppks[1], Power: 2},
			},
			ValsetUpdateId: 1,
		},
		{
			ValidatorUpdates: []abci.ValidatorUpdate{
				{PubKey: ppks[2], Power: 3},
			},
			ValsetUpdateId: 2,
		},
	}
	providerKeeper.AppendPendingPackets(ctx, chainID, packetList...)

	packets := providerKeeper.GetPendingPackets(ctx, chainID)
	require.Len(t, packets, 2)

	newPacket := ccv.ValidatorSetChangePacketData{
		ValidatorUpdates: []abci.ValidatorUpdate{
			{PubKey: ppks[3], Power: 4},
		},
		ValsetUpdateId: 3,
	}
	providerKeeper.AppendPendingPackets(ctx, chainID, newPacket)
	vscs := providerKeeper.GetPendingPackets(ctx, chainID)
	require.Len(t, vscs, 3)
	require.True(t, vscs[len(vscs)-1].ValsetUpdateId == 3)
	require.True(t, vscs[len(vscs)-1].GetValidatorUpdates()[0].PubKey.String() == ppks[3].String())

	providerKeeper.DeletePendingPackets(ctx, chainID)
	pending = providerKeeper.GetPendingPackets(ctx, chainID)
	require.Len(t, pending, 0)
}

// TestInitHeight tests the getter and setter methods for the stored block heights (on provider) when a given consumer chain was started
func TestInitHeight(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	tc := []struct {
		chainID  string
		expected uint64
	}{
		{expected: 0, chainID: "chain"},
		{expected: 10, chainID: "chain1"},
		{expected: 12, chainID: "chain2"},
	}

	providerKeeper.SetInitChainHeight(ctx, tc[1].chainID, tc[1].expected)
	providerKeeper.SetInitChainHeight(ctx, tc[2].chainID, tc[2].expected)

	for _, tc := range tc {
		height, _ := providerKeeper.GetInitChainHeight(ctx, tc.chainID)
		require.Equal(t, tc.expected, height)
	}
}

func TestIterateOverUnbondingOpIndex(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "6"

	// mock an unbonding index
	unbondingOpIndex := []uint64{0, 1, 2, 3, 4, 5, 6}

	// set ubd ops by varying vsc ids and index slices
	for i := 1; i < len(unbondingOpIndex); i++ {
		providerKeeper.SetUnbondingOpIndex(ctx, chainID, uint64(i), unbondingOpIndex[:i])
	}

	// check iterator returns expected entries
	i := 1
	providerKeeper.IterateUnbondingOpIndex(ctx, chainID, func(vscID uint64, ubdIndex []uint64) (stop bool) {
		require.Equal(t, uint64(i), vscID)
		require.EqualValues(t, unbondingOpIndex[:i], ubdIndex)
		i++
		return false // do not stop the iteration
	})
	require.Equal(t, len(unbondingOpIndex), i)
}

func TestMaturedUnbondingOps(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	ids, err := providerKeeper.GetMaturedUnbondingOps(ctx)
	require.NoError(t, err)
	require.Nil(t, ids)

	unbondingOpIds := []uint64{0, 1, 2, 3, 4, 5, 6}
	providerKeeper.AppendMaturedUnbondingOps(ctx, unbondingOpIds)

	ids, err = providerKeeper.ConsumeMaturedUnbondingOps(ctx)
	require.NoError(t, err)
	require.Equal(t, len(unbondingOpIds), len(ids))
	for i := 0; i < len(unbondingOpIds); i++ {
		require.Equal(t, unbondingOpIds[i], ids[i])
	}
}

func TestInitTimeoutTimestamp(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	tc := []struct {
		chainID  string
		expected uint64
	}{
		// ordered alphabetically - descending
		{expected: 5, chainID: "z-chain"},
		{expected: 12, chainID: "b-chain"},
		{expected: 10, chainID: "a-chain"},
	}

	_, found := providerKeeper.GetInitTimeoutTimestamp(ctx, tc[0].chainID)
	require.False(t, found)

	providerKeeper.SetInitTimeoutTimestamp(ctx, tc[0].chainID, tc[0].expected)
	providerKeeper.SetInitTimeoutTimestamp(ctx, tc[1].chainID, tc[1].expected)
	providerKeeper.SetInitTimeoutTimestamp(ctx, tc[2].chainID, tc[2].expected)

	i := 2
	// store is iterated in alphabetical ascending order
	// not in the order of insertion
	providerKeeper.IterateAllInitTimeoutTimestamp(ctx, func(chainID string, ts uint64) {
		require.Equal(t, chainID, tc[i].chainID)
		require.Equal(t, ts, tc[i].expected)
		i--
	})

	for _, tc := range tc {
		ts, found := providerKeeper.GetInitTimeoutTimestamp(ctx, tc.chainID)
		require.True(t, found)
		require.Equal(t, tc.expected, ts)
	}

	providerKeeper.DeleteInitTimeoutTimestamp(ctx, tc[1].chainID)
	_, found = providerKeeper.GetInitTimeoutTimestamp(ctx, tc[1].chainID)
	require.False(t, found)
}

// TestVscSendTimestamp tests the set, deletion, and iteration methods for VSC timeout timestamps
func TestVscSendTimestamp(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := ctx.BlockTime()

	testCases := []struct {
		chainID string
		ts      time.Time
		vscID   uint64
	}{
		{chainID: "chain", ts: now.Add(time.Hour), vscID: 1},
		{chainID: "chain", ts: now.Add(2 * time.Hour), vscID: 2},
		{chainID: "chain1", ts: now.Add(time.Hour), vscID: 1},
		{chainID: "chain2", ts: now.Add(time.Hour), vscID: 1},
	}

	i := 0
	chainID := "chain"
	providerKeeper.IterateVscSendTimestamps(ctx, chainID, func(_ uint64, _ time.Time) (stop bool) {
		i++
		return false // do not stop
	})
	require.Equal(t, 0, i)

	for _, tc := range testCases {
		providerKeeper.SetVscSendTimestamp(ctx, tc.chainID, tc.vscID, tc.ts)
	}

	i = 0
	providerKeeper.IterateVscSendTimestamps(ctx, testCases[0].chainID, func(vscID uint64, ts time.Time) (stop bool) {
		require.Equal(t, vscID, testCases[i].vscID)
		require.Equal(t, ts, testCases[i].ts)
		i++
		return false // do not stop
	})
	require.Equal(t, 2, i)

	// delete VSC send timestamps
	var ids []uint64
	providerKeeper.IterateVscSendTimestamps(ctx, testCases[0].chainID, func(vscID uint64, _ time.Time) (stop bool) {
		ids = append(ids, vscID)
		return false // do not stop
	})
	for _, vscID := range ids {
		providerKeeper.DeleteVscSendTimestamp(ctx, testCases[0].chainID, vscID)
	}

	i = 0
	providerKeeper.IterateVscSendTimestamps(ctx, testCases[0].chainID, func(_ uint64, _ time.Time) (stop bool) {
		i++
		return false // do not stop
	})
	require.Equal(t, 0, i)
}

// TestIterateConsumerChains tests IterateConsumerChains behaviour correctness
func TestIterateConsumerChains(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainIDs := []string{"chain-1", "chain-2"}
	for _, c := range chainIDs {
		pk.SetConsumerClientId(ctx, c, fmt.Sprintf("client-%s", c))
	}

	result := []string{}
	testIterateAll := func(ctx sdk.Context, chainID, clientID string) (stop bool) {
		result = append(result, chainID)
		return false // will not stop iteration
	}

	require.Empty(t, result, "initial result not empty")
	require.Len(t, chainIDs, 2, "initial chainIDs not len 2")

	// iterate and check all chains are returned
	pk.IterateConsumerChains(ctx, testIterateAll)
	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, chainIDs[0], "result does not contain '%s'", chainIDs[0])
	require.Contains(t, result, chainIDs[1], "result does not contain '%s'", chainIDs[1])

	result = []string{}
	testGetFirst := func(ctx sdk.Context, chainID, clientID string) (stop bool) {
		result = append(result, chainID)
		return true // will stop iteration after iterating 1 element
	}
	require.Empty(t, result, "initial result not empty")
	// iterate and check first chain is
	pk.IterateConsumerChains(ctx, testGetFirst)
	require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	require.Contains(t, result, chainIDs[0], "result does not contain '%s'", chainIDs[0])
	require.NotContains(t, result, chainIDs[1], "result should not contain '%s'", chainIDs[1])
}

// TestIterateConsumerChains tests IterateConsumerChains behaviour correctness
func TestIterateChannelToChain(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	type chanToChain struct {
		chainID   string
		channelID string
	}

	cases := []chanToChain{
		{
			chainID:   "chain-1",
			channelID: "channel-1",
		},
		{
			chainID:   "chain-2",
			channelID: "channel-2",
		},
	}

	for _, c := range cases {
		pk.SetChannelToChain(ctx, c.channelID, c.chainID)
	}

	result := []chanToChain{}
	testIterateAll := func(ctx sdk.Context, channelID, chainID string) (stop bool) {
		result = append(result, chanToChain{
			chainID:   chainID,
			channelID: channelID,
		})
		return false // will not stop iteration
	}

	require.Empty(t, result, "initial result not empty")

	// iterate and check all results are returned
	pk.IterateChannelToChain(ctx, testIterateAll)
	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, cases[0], "result does not contain '%s'", cases[0])
	require.Contains(t, result, cases[1], "result does not contain '%s'", cases[1])

	result = []chanToChain{}
	testGetFirst := func(ctx sdk.Context, channelID, chainID string) (stop bool) {
		result = append(result, chanToChain{
			chainID:   chainID,
			channelID: channelID,
		})
		return true // will stop iteration
	}

	require.Empty(t, result, "initial result not empty")
	// iterate and check 1 result is returned
	pk.IterateChannelToChain(ctx, testGetFirst)
	require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	require.Contains(t, result, cases[0], "result does not contain '%s'", cases[0])
	require.NotContains(t, result, cases[1], "result should not contain '%s'", cases[1])
}

// IterateOverUnbondingOps tests IterateOverUnbondingOps behaviour correctness
func TestIterateOverUnbondingOps(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	ops := []ccv.UnbondingOp{
		{
			Id:                      1,
			UnbondingConsumerChains: []string{"test"},
		},
		{
			Id:                      2,
			UnbondingConsumerChains: []string{"test"},
		},
	}

	for _, op := range ops {
		pk.SetUnbondingOp(ctx, op)
	}

	result := []ccv.UnbondingOp{}
	testIterateAll := func(id uint64, ubdOp ccv.UnbondingOp) (stop bool) {
		result = append(result, ubdOp)
		return false // will not stop iteration
	}

	require.Empty(t, result, "initial result not empty")

	// iterate and check all results are returned
	pk.IterateUnbondingOps(ctx, testIterateAll)
	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, ops[0], "result does not contain '%s'", ops[0])
	require.Contains(t, result, ops[1], "result does not contain '%s'", ops[1])

	result = []ccv.UnbondingOp{}
	testGetFirst := func(id uint64, ubdOp ccv.UnbondingOp) (stop bool) {
		result = append(result, ubdOp)
		return true // will stop iteration
	}

	require.Empty(t, result, "initial result not empty")
	// iterate and check 1 result is returned
	pk.IterateUnbondingOps(ctx, testGetFirst)
	require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	require.Contains(t, result, ops[0], "result does not contain '%s'", ops[0])
	require.NotContains(t, result, ops[1], "result should not contain '%s'", ops[1])
}
