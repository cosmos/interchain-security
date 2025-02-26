package keeper_test

import (
	"fmt"
	"sort"
	"testing"

	ibctesting "github.com/cosmos/ibc-go/v10/testing"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	abci "github.com/cometbft/cometbft/abci/types"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"

	cryptotestutil "github.com/cosmos/interchain-security/v7/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v7/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

const (
	CONSUMER_CHAIN_ID = "chain-id"
	CONSUMER_ID       = "0"
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

// TestGetAllValsetUpdateBlockHeights tests GetAllValsetUpdateBlockHeights behaviour correctness
func TestGetAllValsetUpdateBlockHeights(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	cases := []providertypes.ValsetUpdateIdToHeight{
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

	chainID := CONSUMER_CHAIN_ID

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

	chainID := CONSUMER_CHAIN_ID

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

func TestGetAllConsumersWithIBCClients(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerIds := []string{"2", "1", "4", "3"}
	for i, consumerId := range consumerIds {
		clientId := fmt.Sprintf("client-%d", len(consumerIds)-i)
		pk.SetConsumerClientId(ctx, consumerId, clientId)
		pk.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)
	}

	actualConsumerIds := pk.GetAllConsumersWithIBCClients(ctx)
	require.Len(t, actualConsumerIds, len(consumerIds))

	// sort the consumer ids before comparing they are equal
	sort.Slice(consumerIds, func(i, j int) bool {
		return consumerIds[i] < consumerIds[j]
	})
	sort.Slice(actualConsumerIds, func(i, j int) bool {
		return actualConsumerIds[i] < actualConsumerIds[j]
	})
	require.Equal(t, consumerIds, actualConsumerIds)
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

// TestConsumerCommissionRate tests the `SetConsumerCommissionRate`, `GetConsumerCommissionRate`, and `DeleteConsumerCommissionRate` methods
func TestConsumerCommissionRate(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr1 := providertypes.NewProviderConsAddress([]byte("providerAddr1"))
	providerAddr2 := providertypes.NewProviderConsAddress([]byte("providerAddr2"))

	cr, found := providerKeeper.GetConsumerCommissionRate(ctx, CONSUMER_ID, providerAddr1)
	require.False(t, found)
	require.Equal(t, math.LegacyZeroDec(), cr)

	providerKeeper.SetConsumerCommissionRate(ctx, CONSUMER_ID, providerAddr1, math.LegacyOneDec())
	cr, found = providerKeeper.GetConsumerCommissionRate(ctx, CONSUMER_ID, providerAddr1)
	require.True(t, found)
	require.Equal(t, math.LegacyOneDec(), cr)

	providerKeeper.SetConsumerCommissionRate(ctx, CONSUMER_ID, providerAddr2, math.LegacyZeroDec())
	cr, found = providerKeeper.GetConsumerCommissionRate(ctx, CONSUMER_ID, providerAddr2)
	require.True(t, found)
	require.Equal(t, math.LegacyZeroDec(), cr)

	provAddrs := providerKeeper.GetAllCommissionRateValidators(ctx, CONSUMER_ID)
	require.Len(t, provAddrs, 2)

	for _, addr := range provAddrs {
		providerKeeper.DeleteConsumerCommissionRate(ctx, CONSUMER_ID, addr)
	}

	_, found = providerKeeper.GetConsumerCommissionRate(ctx, CONSUMER_ID, providerAddr1)
	require.False(t, found)

	_, found = providerKeeper.GetConsumerCommissionRate(ctx, CONSUMER_ID, providerAddr2)
	require.False(t, found)
}

// TestConsumerClientId tests the getter, setter, and deletion of the client id <> consumer id mappings
func TestConsumerClientId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "123"
	clientIds := []string{"clientId1", "clientId2"}

	_, found := providerKeeper.GetConsumerClientId(ctx, consumerId)
	require.False(t, found)
	_, found = providerKeeper.GetClientIdToConsumerId(ctx, clientIds[0])
	require.False(t, found)
	_, found = providerKeeper.GetClientIdToConsumerId(ctx, clientIds[1])
	require.False(t, found)

	providerKeeper.SetConsumerClientId(ctx, consumerId, clientIds[0])
	res, found := providerKeeper.GetConsumerClientId(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, clientIds[0], res)
	res, found = providerKeeper.GetClientIdToConsumerId(ctx, clientIds[0])
	require.True(t, found)
	require.Equal(t, consumerId, res)
	_, found = providerKeeper.GetClientIdToConsumerId(ctx, clientIds[1])
	require.False(t, found)

	// overwrite the client ID
	providerKeeper.SetConsumerClientId(ctx, consumerId, clientIds[1])
	res, found = providerKeeper.GetConsumerClientId(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, clientIds[1], res)
	res, found = providerKeeper.GetClientIdToConsumerId(ctx, clientIds[1])
	require.True(t, found)
	require.Equal(t, consumerId, res)
	_, found = providerKeeper.GetClientIdToConsumerId(ctx, clientIds[0])
	require.False(t, found)

	providerKeeper.DeleteConsumerClientId(ctx, consumerId)
	_, found = providerKeeper.GetConsumerClientId(ctx, consumerId)
	require.False(t, found)
	_, found = providerKeeper.GetClientIdToConsumerId(ctx, clientIds[0])
	require.False(t, found)
	_, found = providerKeeper.GetClientIdToConsumerId(ctx, clientIds[1])
	require.False(t, found)
}
