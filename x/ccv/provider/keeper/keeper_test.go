package keeper_test

import (
	"fmt"
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	ibcsimapp "github.com/cosmos/ibc-go/v3/testing/simapp"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"

	"github.com/stretchr/testify/require"
)

// TestValsetUpdateBlockHeight tests the getter, setter, and deletion methods for valset updates mapped to block height
func TestValsetUpdateBlockHeight(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	blockHeight, found := providerKeeper.GetValsetUpdateBlockHeight(ctx, uint64(0))
	require.False(t, found)
	require.Zero(t, blockHeight)

	providerKeeper.SetValsetUpdateBlockHeight(ctx, uint64(1), uint64(2))
	blockHeight, found = providerKeeper.GetValsetUpdateBlockHeight(ctx, uint64(1))
	require.True(t, found)
	require.Equal(t, blockHeight, uint64(2))

	providerKeeper.DeleteValsetUpdateBlockHeight(ctx, uint64(1))
	blockHeight, found = providerKeeper.GetValsetUpdateBlockHeight(ctx, uint64(1))
	require.False(t, found)
	require.Zero(t, blockHeight)

	providerKeeper.SetValsetUpdateBlockHeight(ctx, uint64(1), uint64(2))
	providerKeeper.SetValsetUpdateBlockHeight(ctx, uint64(3), uint64(4))
	blockHeight, found = providerKeeper.GetValsetUpdateBlockHeight(ctx, uint64(3))
	require.True(t, found)
	require.Equal(t, blockHeight, uint64(4))
}

// TestSlashAcks tests the getter, setter, iteration, and deletion methods for stored slash acknowledgements
func TestSlashAcks(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

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

	for _, c := range chains {
		require.Equal(t, p, providerKeeper.GetSlashAcks(ctx, c))
	}
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

	pending := providerKeeper.GetPendingVSCPackets(ctx, chainID)
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
	providerKeeper.AppendPendingVSCPackets(ctx, chainID, packetList...)

	packets := providerKeeper.GetPendingVSCPackets(ctx, chainID)
	require.Len(t, packets, 2)

	newPacket := ccv.ValidatorSetChangePacketData{
		ValidatorUpdates: []abci.ValidatorUpdate{
			{PubKey: ppks[3], Power: 4},
		},
		ValsetUpdateId: 3,
	}
	providerKeeper.AppendPendingVSCPackets(ctx, chainID, newPacket)
	vscs := providerKeeper.GetPendingVSCPackets(ctx, chainID)
	require.Len(t, vscs, 3)
	require.True(t, vscs[len(vscs)-1].ValsetUpdateId == 3)
	require.True(t, vscs[len(vscs)-1].GetValidatorUpdates()[0].PubKey.String() == ppks[3].String())

	providerKeeper.DeletePendingVSCPackets(ctx, chainID)
	pending = providerKeeper.GetPendingVSCPackets(ctx, chainID)
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

// TestGetAllUnbondingOpIndexes tests GetAllUnbondingOpIndexes behavior correctness
func TestGetAllUnbondingOpIndexes(t *testing.T) {

	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chain-1"

	cases := []types.VscUnbondingOps{
		{
			VscId:          2,
			UnbondingOpIds: []uint64{1, 2, 3, 4, 5, 6},
		},
		{
			VscId:          1,
			UnbondingOpIds: []uint64{1, 2, 3},
		},
	}

	pk.SetUnbondingOpIndex(ctx, "chain-2", 1, []uint64{1, 2, 3})
	for _, c := range cases {
		pk.SetUnbondingOpIndex(ctx, chainID, c.VscId, c.UnbondingOpIds)
	}

	// iterate and check all results are returned
	result := pk.GetAllUnbondingOpIndexes(ctx, chainID)
	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, cases[0], "result does not contain '%s'", cases[0])
	require.Contains(t, result, cases[1], "result does not contain '%s'", cases[1])

	result = []types.VscUnbondingOps{}
	require.Empty(t, result, "initial result not empty")

	// iterate and check first index is with vscID 1
	for _, index := range pk.GetAllUnbondingOpIndexes(ctx, chainID) {
		result = append(result, index)
		break
	}
	require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	require.Contains(t, result, cases[1], "result does not contain '%s'", cases[1])
	require.NotContains(t, result, cases[0], "result should not contain '%s'", cases[0])
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
	for _, initTimeoutTimestamp := range providerKeeper.GetAllInitTimeoutTimestamps(ctx) {
		require.Equal(t, initTimeoutTimestamp.ChainId, tc[i].chainID)
		require.Equal(t, initTimeoutTimestamp.Timestamp, tc[i].expected)
		i--
	}

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
	for _, _ = range providerKeeper.GetAllVscSendTimestamps(ctx, chainID) {
		i++
	}
	require.Equal(t, 0, i)

	for _, tc := range testCases {
		providerKeeper.SetVscSendTimestamp(ctx, tc.chainID, tc.vscID, tc.ts)
	}

	i = 0
	for _, vscSendTimestamp := range providerKeeper.GetAllVscSendTimestamps(ctx, testCases[0].chainID) {
		require.Equal(t, vscSendTimestamp.VscId, testCases[i].vscID)
		require.Equal(t, vscSendTimestamp.Timestamp, testCases[i].ts)
		i++
	}
	require.Equal(t, 2, i)

	// delete VSC send timestamps
	for _, vscSendTimestamp := range providerKeeper.GetAllVscSendTimestamps(ctx, testCases[0].chainID) {
		providerKeeper.DeleteVscSendTimestamp(ctx, testCases[0].chainID, vscSendTimestamp.VscId)
	}

	i = 0
	for _, _ = range providerKeeper.GetAllVscSendTimestamps(ctx, testCases[0].chainID) {
		i++
	}
	require.Equal(t, 0, i)
}

// TestGetAllConsumerChains tests GetAllConsumerChains behaviour correctness
func TestGetAllConsumerChains(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainIDs := []string{"chain-2", "chain-1"}
	for _, c := range chainIDs {
		pk.SetConsumerClientId(ctx, c, fmt.Sprintf("client-%s", c))
	}

	result := []string{}

	require.Empty(t, result, "initial result not empty")
	require.Len(t, chainIDs, 2, "initial chainIDs not len 2")

	// iterate and check all chains are returned
	for _, chain := range pk.GetAllConsumerChains(ctx) {
		result = append(result, chain.ChainId)
	}

	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, chainIDs[0], "result does not contain '%s'", chainIDs[0])
	require.Contains(t, result, chainIDs[1], "result does not contain '%s'", chainIDs[1])

	result = []string{}
	require.Empty(t, result, "initial result not empty")

	// iterate and check first chain is chain-1
	for _, chain := range pk.GetAllConsumerChains(ctx) {
		result = append(result, chain.ChainId)
		break
	}
	require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	require.Contains(t, result, chainIDs[1], "result does not contain '%s'", chainIDs[1])
	require.NotContains(t, result, chainIDs[0], "result should not contain '%s'", chainIDs[0])
}

// TestGetAllChannelToChains tests GetAllChannelToChains behaviour correctness
func TestGetAllChannelToChains(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	cases := []types.ChannelToChain{
		{
			ChainId:   "chain-2",
			ChannelId: "channel-2",
		},
		{
			ChainId:   "chain-1",
			ChannelId: "channel-1",
		},
	}

	for _, c := range cases {
		pk.SetChannelToChain(ctx, c.ChannelId, c.ChainId)
	}

	// iterate and check all results are returned
	result := pk.GetAllChannelToChains(ctx)
	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, cases[0], "result does not contain '%s'", cases[0])
	require.Contains(t, result, cases[1], "result does not contain '%s'", cases[1])

	result = []types.ChannelToChain{}
	require.Empty(t, result, "initial result not empty")

	// iterate and check first mapping is <chain-1: channel-1>
	for _, channelToChain := range pk.GetAllChannelToChains(ctx) {
		result = append(result, channelToChain)
		break
	}
	require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	require.Contains(t, result, cases[1], "result does not contain '%s'", cases[1])
	require.NotContains(t, result, cases[0], "result should not contain '%s'", cases[0])
}

// TestGetAllUnbondingOps tests GetAllUnbondingOps behaviour correctness
func TestGetAllUnbondingOps(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	ops := []types.UnbondingOp{
		{
			Id:                      2,
			UnbondingConsumerChains: []string{"chain-2", "chain-1"},
		},
		{
			Id:                      1,
			UnbondingConsumerChains: []string{"chain-1", "chain-2"},
		},
	}

	for _, op := range ops {
		pk.SetUnbondingOp(ctx, op)
	}

	// iterate and check all results are returned
	result := pk.GetAllUnbondingOps(ctx)
	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, ops[0], "result does not contain '%s'", ops[0])
	require.Contains(t, result, ops[1], "result does not contain '%s'", ops[1])

	result = []types.UnbondingOp{}
	require.Empty(t, result, "initial result not empty")

	// iterate and check first op has ID 1
	for _, unbondingOp := range pk.GetAllUnbondingOps(ctx) {
		result = append(result, unbondingOp)
		break
	}
	require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	require.Contains(t, result, ops[1], "result does not contain '%s'", ops[1])
	require.NotContains(t, result, ops[0], "result should not contain '%s'", ops[0])
}

// TestGetAllValsetUpdateBlockHeights tests GetAllValsetUpdateBlockHeights behaviour correctness
func TestGetAllValsetUpdateBlockHeights(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	cases := []types.ValsetUpdateIdToHeight{
		{
			ValsetUpdateId: 2,
			Height:         22,
		},
		{
			ValsetUpdateId: 1,
			Height:         11,
		},
	}

	for _, c := range cases {
		pk.SetValsetUpdateBlockHeight(ctx, c.ValsetUpdateId, c.Height)
	}

	// iterate and check all results are returned
	result := pk.GetAllValsetUpdateBlockHeights(ctx)
	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, cases[0], "result does not contain '%s'", cases[0])
	require.Contains(t, result, cases[1], "result does not contain '%s'", cases[1])

	result = []types.ValsetUpdateIdToHeight{}
	require.Empty(t, result, "initial result not empty")

	// iterate and check first op has ID 1
	for _, vscIDtoHeight := range pk.GetAllValsetUpdateBlockHeights(ctx) {
		result = append(result, vscIDtoHeight)
		break
	}
	require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	require.Contains(t, result, cases[1], "result does not contain '%s'", cases[1])
	require.NotContains(t, result, cases[0], "result should not contain '%s'", cases[0])
}
