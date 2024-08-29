package keeper_test

import (
	"bytes"
	"fmt"
	"sort"
	"testing"

	"cosmossdk.io/math"
	ibctesting "github.com/cosmos/ibc-go/v8/testing"
	"github.com/stretchr/testify/require"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"

	abci "github.com/cometbft/cometbft/abci/types"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"

	cryptotestutil "github.com/cosmos/interchain-security/v5/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

const consumer = "consumer"

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
		{
			// normal execution should not have two ValsetUpdateIdToHeight
			// with the same Height, but let's test it anyway
			ValsetUpdateId: 4,
			Height:         11,
		},
		{
			ValsetUpdateId: 3,
			Height:         33,
		},
	}
	expectedGetAllOrder := cases
	// sorting by ValsetUpdateId
	sort.Slice(expectedGetAllOrder, func(i, j int) bool {
		return expectedGetAllOrder[i].ValsetUpdateId < expectedGetAllOrder[j].ValsetUpdateId
	})

	for _, c := range cases {
		pk.SetValsetUpdateBlockHeight(ctx, c.ValsetUpdateId, c.Height)
	}

	// iterate and check all results are returned in the expected order
	result := pk.GetAllValsetUpdateBlockHeights(ctx)
	require.Len(t, result, len(cases))
	require.Equal(t, expectedGetAllOrder, result)
}

// TestSlashAcks tests the getter, setter, iteration, and deletion methods for stored slash acknowledgements
func TestSlashAcks(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := consumer

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
		providerKeeper.DeleteSlashAcks(ctx, c)
		acks = providerKeeper.GetSlashAcks(ctx, c)
		require.Len(t, acks, 0)
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

	chainID := consumer

	pending := providerKeeper.GetPendingVSCPackets(ctx, chainID)
	require.Len(t, pending, 0)

	_, pks, _ := ibctesting.GenerateKeys(t, 4)
	var ppks [4]tmprotocrypto.PublicKey
	for i, pk := range pks {
		ppks[i], _ = cryptocodec.ToCmtProtoPublicKey(pk)
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

func TestGetAllRegisteredConsumerChainIDs(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainIDs := []string{"chain-2", "chain-1", "chain-4", "chain-3"}
	// GetAllRegisteredConsumerIds iterates over consumerId in lexicographical order
	expectedChainIDs := []string{"chain-1", "chain-2", "chain-3", "chain-4"}

	for i, chainID := range chainIDs {
		clientID := fmt.Sprintf("client-%d", len(chainIDs)-i)
		pk.SetConsumerClientId(ctx, chainID, clientID)
	}

	result := pk.GetAllRegisteredConsumerIds(ctx)
	require.Len(t, result, len(chainIDs))
	require.Equal(t, expectedChainIDs, result)
}

// TestGetAllChannelToChains tests GetAllChannelToConsumers behaviour correctness
func TestGetAllChannelToChains(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerIds := []string{"2", "1", "4", "3"}
	var expectedGetAllOrder []struct {
		ChannelId  string
		ConsumerId string
	}

	for i, consumerId := range consumerIds {
		channelID := fmt.Sprintf("client-%d", len(consumerIds)-i)
		pk.SetChannelToConsumerId(ctx, channelID, consumerId)
		expectedGetAllOrder = append(expectedGetAllOrder, struct {
			ChannelId  string
			ConsumerId string
		}{ConsumerId: consumerId, ChannelId: channelID})
	}
	// sorting by channelID
	sort.Slice(expectedGetAllOrder, func(i, j int) bool {
		return expectedGetAllOrder[i].ChannelId < expectedGetAllOrder[j].ChannelId
	})

	result := pk.GetAllChannelToConsumers(ctx)
	require.Len(t, result, len(consumerIds))
	require.Equal(t, expectedGetAllOrder, result)
}

// TestSetSlashLog tests slash log getter and setter methods
func TestSetSlashLog(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	addrWithDoubleSigns := cryptotestutil.NewCryptoIdentityFromIntSeed(1).ProviderConsAddress()
	addrWithoutDoubleSigns := cryptotestutil.NewCryptoIdentityFromIntSeed(2).ProviderConsAddress()

	providerKeeper.SetSlashLog(ctx, addrWithDoubleSigns)
	require.True(t, providerKeeper.GetSlashLog(ctx, addrWithDoubleSigns))
	require.False(t, providerKeeper.GetSlashLog(ctx, addrWithoutDoubleSigns))
}

func TestGetAllOptedIn(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	expectedOptedInValidators := []types.ProviderConsAddress{
		types.NewProviderConsAddress([]byte("providerAddr1")),
		types.NewProviderConsAddress([]byte("providerAddr2")),
		types.NewProviderConsAddress([]byte("providerAddr3")),
	}

	for _, expectedOptedInValidator := range expectedOptedInValidators {
		providerKeeper.SetOptedIn(ctx, "consumerId", expectedOptedInValidator)
	}

	actualOptedInValidators := providerKeeper.GetAllOptedIn(ctx, "consumerId")

	// sort validators first to be able to compare
	sortOptedInValidators := func(addresses []types.ProviderConsAddress) {
		sort.Slice(addresses, func(i, j int) bool {
			return bytes.Compare(addresses[i].ToSdkConsAddr(), addresses[j].ToSdkConsAddr()) < 0
		})
	}
	sortOptedInValidators(expectedOptedInValidators)
	sortOptedInValidators(actualOptedInValidators)
	require.Equal(t, expectedOptedInValidators, actualOptedInValidators)
}

// TestOptedIn tests the `SetOptedIn`, `IsOptedIn`, `DeleteOptedIn` and `DeleteAllOptedIn` methods
func TestOptedIn(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	optedInValidator1 := types.NewProviderConsAddress([]byte("providerAddr1"))
	optedInValidator2 := types.NewProviderConsAddress([]byte("providerAddr2"))

	require.False(t, providerKeeper.IsOptedIn(ctx, "consumerId", optedInValidator1))
	providerKeeper.SetOptedIn(ctx, "consumerId", optedInValidator1)
	require.True(t, providerKeeper.IsOptedIn(ctx, "consumerId", optedInValidator1))
	providerKeeper.DeleteOptedIn(ctx, "consumerId", optedInValidator1)
	require.False(t, providerKeeper.IsOptedIn(ctx, "consumerId", optedInValidator1))

	providerKeeper.SetOptedIn(ctx, "consumerId", optedInValidator1)
	providerKeeper.SetOptedIn(ctx, "consumerId", optedInValidator2)
	require.True(t, providerKeeper.IsOptedIn(ctx, "consumerId", optedInValidator1))
	require.True(t, providerKeeper.IsOptedIn(ctx, "consumerId", optedInValidator2))
	providerKeeper.DeleteAllOptedIn(ctx, "consumerId")
	require.False(t, providerKeeper.IsOptedIn(ctx, "consumerId", optedInValidator1))
	require.False(t, providerKeeper.IsOptedIn(ctx, "consumerId", optedInValidator2))
}

// TestConsumerCommissionRate tests the `SetConsumerCommissionRate`, `GetConsumerCommissionRate`, and `DeleteConsumerCommissionRate` methods
func TestConsumerCommissionRate(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr1 := types.NewProviderConsAddress([]byte("providerAddr1"))
	providerAddr2 := types.NewProviderConsAddress([]byte("providerAddr2"))

	cr, found := providerKeeper.GetConsumerCommissionRate(ctx, "consumerId", providerAddr1)
	require.False(t, found)
	require.Equal(t, math.LegacyZeroDec(), cr)

	providerKeeper.SetConsumerCommissionRate(ctx, "consumerId", providerAddr1, math.LegacyOneDec())
	cr, found = providerKeeper.GetConsumerCommissionRate(ctx, "consumerId", providerAddr1)
	require.True(t, found)
	require.Equal(t, math.LegacyOneDec(), cr)

	providerKeeper.SetConsumerCommissionRate(ctx, "consumerId", providerAddr2, math.LegacyZeroDec())
	cr, found = providerKeeper.GetConsumerCommissionRate(ctx, "consumerId", providerAddr2)
	require.True(t, found)
	require.Equal(t, math.LegacyZeroDec(), cr)

	provAddrs := providerKeeper.GetAllCommissionRateValidators(ctx, "consumerId")
	require.Len(t, provAddrs, 2)

	for _, addr := range provAddrs {
		providerKeeper.DeleteConsumerCommissionRate(ctx, "consumerId", addr)
	}

	_, found = providerKeeper.GetConsumerCommissionRate(ctx, "consumerId", providerAddr1)
	require.False(t, found)

	_, found = providerKeeper.GetConsumerCommissionRate(ctx, "consumerId", providerAddr2)
	require.False(t, found)
}

// TestAllowlist tests the `SetAllowlist`, `IsAllowlisted`, `DeleteAllowlist`, and `IsAllowlistEmpty` methods
func TestAllowlist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "consumerId"

	// no validator was allowlisted and hence the allowlist is empty
	require.True(t, providerKeeper.IsAllowlistEmpty(ctx, chainID))

	providerAddr1 := types.NewProviderConsAddress([]byte("providerAddr1"))
	providerKeeper.SetAllowlist(ctx, chainID, providerAddr1)
	require.True(t, providerKeeper.IsAllowlisted(ctx, chainID, providerAddr1))

	// allowlist is not empty anymore
	require.False(t, providerKeeper.IsAllowlistEmpty(ctx, chainID))

	providerAddr2 := types.NewProviderConsAddress([]byte("providerAddr2"))
	providerKeeper.SetAllowlist(ctx, chainID, providerAddr2)
	require.True(t, providerKeeper.IsAllowlisted(ctx, chainID, providerAddr2))
	require.False(t, providerKeeper.IsAllowlistEmpty(ctx, chainID))

	providerKeeper.DeleteAllowlist(ctx, chainID)
	require.False(t, providerKeeper.IsAllowlisted(ctx, chainID, providerAddr1))
	require.False(t, providerKeeper.IsAllowlisted(ctx, chainID, providerAddr2))
	require.True(t, providerKeeper.IsAllowlistEmpty(ctx, chainID))
}

// TestDenylist tests the `SetDenylist`, `IsDenylisted`, `DeleteDenylist`, and `IsDenylistEmpty` methods
func TestDenylist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "consumerId"

	// no validator was denylisted and hence the denylist is empty
	require.True(t, providerKeeper.IsDenylistEmpty(ctx, chainID))

	providerAddr1 := types.NewProviderConsAddress([]byte("providerAddr1"))
	providerKeeper.SetDenylist(ctx, chainID, providerAddr1)
	require.True(t, providerKeeper.IsDenylisted(ctx, chainID, providerAddr1))

	// denylist is not empty anymore
	require.False(t, providerKeeper.IsDenylistEmpty(ctx, chainID))

	providerAddr2 := types.NewProviderConsAddress([]byte("providerAddr2"))
	providerKeeper.SetDenylist(ctx, chainID, providerAddr2)
	require.True(t, providerKeeper.IsDenylisted(ctx, chainID, providerAddr2))
	require.False(t, providerKeeper.IsDenylistEmpty(ctx, chainID))

	providerKeeper.DeleteDenylist(ctx, chainID)
	require.False(t, providerKeeper.IsDenylisted(ctx, chainID, providerAddr1))
	require.False(t, providerKeeper.IsDenylisted(ctx, chainID, providerAddr2))
	require.True(t, providerKeeper.IsDenylistEmpty(ctx, chainID))
}

// Tests setting, getting and deleting parameters that are stored per-consumer chain.
// The tests cover the following parameters:
// - MinimumPowerInTopN
func TestKeeperConsumerParams(t *testing.T) {
	k, ctx, _, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

	tests := []struct {
		name         string
		settingFunc  func(sdk.Context, string, int64)
		getFunc      func(sdk.Context, string) int64
		deleteFunc   func(sdk.Context, string)
		initialValue int64
		updatedValue int64
	}{
		{
			name:        "Minimum Power In Top N",
			settingFunc: func(ctx sdk.Context, id string, val int64) { k.SetMinimumPowerInTopN(ctx, id, val) },
			getFunc: func(ctx sdk.Context, id string) int64 {
				minimumPowerInTopN, _ := k.GetMinimumPowerInTopN(ctx, id)
				return minimumPowerInTopN
			},
			deleteFunc:   func(ctx sdk.Context, id string) { k.DeleteMinimumPowerInTopN(ctx, id) },
			initialValue: 1000,
			updatedValue: 2000,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			chainID := "consumerId"
			// Set initial value
			tt.settingFunc(ctx, chainID, int64(tt.initialValue))

			// Retrieve and check initial value
			actualValue := tt.getFunc(ctx, chainID)
			require.EqualValues(t, tt.initialValue, actualValue)

			// Update value
			tt.settingFunc(ctx, chainID, int64(tt.updatedValue))

			// Retrieve and check updated value
			newActualValue := tt.getFunc(ctx, chainID)
			require.EqualValues(t, tt.updatedValue, newActualValue)

			// Check non-existent consumer id
			res := tt.getFunc(ctx, "not the consumerId")
			require.Zero(t, res)

			// Delete value
			tt.deleteFunc(ctx, chainID)

			// Check that value was deleted
			res = tt.getFunc(ctx, chainID)
			require.Zero(t, res)

			// Try deleting again
			tt.deleteFunc(ctx, chainID)

			// Check that the value is still deleted
			res = tt.getFunc(ctx, chainID)
			require.Zero(t, res)
		})
	}
}
