package keeper_test

import (
	"fmt"
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	ibcsimapp "github.com/cosmos/ibc-go/v3/testing/simapp"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"

	providerkeepertypes "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
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

	var chainsAcks [][]string

	penaltiesfN := func() (penalties []string) {
		providerKeeper.IterateSlashAcks(ctx, func(id string, acks []string) (stop bool) {
			chainsAcks = append(chainsAcks, acks)
			return false // do not stop iteration
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
	for _, unbondingOpsIndex := range providerKeeper.IterateOverUnbondingOpIndex(ctx, chainID) {
		require.Equal(t, uint64(i), unbondingOpsIndex.VscId)
		require.EqualValues(t, unbondingOpIndex[:i], unbondingOpsIndex.UnbondingOpIds)
		i++
	}

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
	for _, initTimeoutTimestamp := range providerKeeper.IterateInitTimeoutTimestamp(ctx) {
		require.Equal(t, initTimeoutTimestamp.ChainID, tc[i].chainID)
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
	for _, _ = range providerKeeper.IterateVscSendTimestamps(ctx, chainID) {
		i++
	}
	require.Equal(t, 0, i)

	for _, tc := range testCases {
		providerKeeper.SetVscSendTimestamp(ctx, tc.chainID, tc.vscID, tc.ts)
	}

	i = 0
	for _, vscSendTimestamp := range providerKeeper.IterateVscSendTimestamps(ctx, testCases[0].chainID) {
		require.Equal(t, vscSendTimestamp.VscID, testCases[i].vscID)
		require.Equal(t, vscSendTimestamp.Timestamp, testCases[i].ts)
		i++
	}
	require.Equal(t, 2, i)

	// delete VSC send timestamps
	for _, vscSendTimestamp := range providerKeeper.IterateVscSendTimestamps(ctx, testCases[0].chainID) {
		providerKeeper.DeleteVscSendTimestamp(ctx, testCases[0].chainID, vscSendTimestamp.VscID)
	}

	i = 0
	for _, _ = range providerKeeper.IterateVscSendTimestamps(ctx, testCases[0].chainID) {
		i++
	}
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

	require.Empty(t, result, "initial result not empty")
	require.Len(t, chainIDs, 2, "initial chainIDs not len 2")

	// iterate and check all chains are returned
	for _, chain := range pk.IterateConsumerChains(ctx) {
		result = append(result, chain.ChainId)
	}

	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, chainIDs[0], "result does not contain '%s'", chainIDs[0])
	require.Contains(t, result, chainIDs[1], "result does not contain '%s'", chainIDs[1])

	result = []string{}
	require.Empty(t, result, "initial result not empty")

	// iterate and check first chain is
	for _, chain := range pk.IterateConsumerChains(ctx) {
		result = append(result, chain.ChainId)
		break
	}
	require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	require.Contains(t, result, chainIDs[0], "result does not contain '%s'", chainIDs[0])
	require.NotContains(t, result, chainIDs[1], "result should not contain '%s'", chainIDs[1])
}

// TestIterateConsumerChains tests IterateConsumerChains behaviour correctness
func TestIterateChannelToChain(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	cases := []providerkeepertypes.ChannelToChain{
		{
			ChainID:   "chain-1",
			ChannelID: "channel-1",
		},
		{
			ChainID:   "chain-2",
			ChannelID: "channel-2",
		},
	}

	for _, c := range cases {
		pk.SetChannelToChain(ctx, c.ChannelID, c.ChainID)
	}

	// iterate and check all results are returned
	result := pk.IterateChannelToChain(ctx)
	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, cases[0], "result does not contain '%s'", cases[0])
	require.Contains(t, result, cases[1], "result does not contain '%s'", cases[1])

	// TODO JEHAN: if it is necessary to stop the iteration, fix this test
	// iterate and check 1 result is returned
	// result = pk.IterateChannelToChain(ctx)
	// require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	// require.Contains(t, result, cases[0], "result does not contain '%s'", cases[0])
	// require.NotContains(t, result, cases[1], "result should not contain '%s'", cases[1])
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

	// iterate and check all results are returned
	result := pk.IterateOverUnbondingOps(ctx)
	require.Len(t, result, 2, "wrong result len - should be 2, got %d", len(result))
	require.Contains(t, result, ops[0], "result does not contain '%s'", ops[0])
	require.Contains(t, result, ops[1], "result does not contain '%s'", ops[1])

	// TODO JEHAN: if it is necessary to stop the iteration, fix this test
	// iterate and check 1 result is returned
	// result = pk.IterateOverUnbondingOps(ctx)
	// require.Len(t, result, 1, "wrong result len - should be 1, got %d", len(result))
	// require.Contains(t, result, ops[0], "result does not contain '%s'", ops[0])
	// require.NotContains(t, result, ops[1], "result should not contain '%s'", ops[1])
}
