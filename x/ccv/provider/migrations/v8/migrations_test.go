package v8

import (
	"testing"
	"time"

	"github.com/golang/mock/gomock"

	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	testutil "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
)

func legacyConsumerAddrsToPruneKey(chainID string, vscID uint64) []byte {
	return providertypes.ChainIdAndUintIdKey(LegacyConsumerAddrsToPruneBytePrefix, chainID, vscID)
}

func legacyAppendConsumerAddrsToPrune(
	store storetypes.KVStore,
	chainID string,
	vscID uint64,
	consumerAddr providertypes.ConsumerConsAddress,
) {
	bz := store.Get(legacyConsumerAddrsToPruneKey(chainID, vscID))
	var consumerAddrsToPrune providertypes.AddressList
	if bz != nil {
		err := consumerAddrsToPrune.Unmarshal(bz)
		if err != nil {
			// An error here would indicate something is very wrong,
			// the data bytes are assumed to be correctly serialized by previous calls to this method.
			panic(err)
		}
	}
	consumerAddrsToPrune.Addresses = append(consumerAddrsToPrune.Addresses, consumerAddr.ToSdkConsAddr())
	bz, err := consumerAddrsToPrune.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// consumerAddrsToPrune is instantiated in this method and should be able to be marshaled.
		panic(err)
	}
	store.Set(legacyConsumerAddrsToPruneKey(chainID, vscID), bz)
}

func legacyVscSendingTimestampKey(chainID string, vscID uint64) []byte {
	return providertypes.ChainIdAndUintIdKey(LegacyVscSendTimestampBytePrefix, chainID, vscID)
}

func legacySetVscSendTimestamp(
	store storetypes.KVStore,
	chainID string,
	vscID uint64,
	timestamp time.Time,
) {
	// Convert timestamp into bytes for storage
	timeBz := sdk.FormatTimeBytes(timestamp)

	store.Set(legacyVscSendingTimestampKey(chainID, vscID), timeBz)
}

func TestMigrateConsumerAddrsToPrune(t *testing.T) {
	t.Helper()
	inMemParams := testutil.NewInMemKeeperParams(t)
	pk, ctx, ctrl, mocks := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	store := ctx.KVStore(inMemParams.StoreKey)

	consumerAddrsToPrune := []struct {
		chainId string
		vscId   uint64
		address providertypes.ConsumerConsAddress
	}{
		{"chain-1", 1, providertypes.NewConsumerConsAddress([]byte{0x01})},
		{"chain-1", 1, providertypes.NewConsumerConsAddress([]byte{0x02})},
		{"chain-2", 1, providertypes.NewConsumerConsAddress([]byte{0x03})},
		{"chain-1", 2, providertypes.NewConsumerConsAddress([]byte{0x04})},
		{"chain-1", 3, providertypes.NewConsumerConsAddress([]byte{0x05})},
	}
	for _, x := range consumerAddrsToPrune {
		legacyAppendConsumerAddrsToPrune(store, x.chainId, x.vscId, x.address)
	}

	ts1 := time.Now().UTC()
	ts2 := ts1.Add(time.Minute).UTC()
	ts3 := ts2.Add(time.Hour).UTC()
	vscSendTimestamps := []struct {
		chainId string
		vscId   uint64
		ts      time.Time
	}{
		{"chain-1", 1, ts1},
		{"chain-1", 2, ts2},
		{"chain-1", 3, ts3},
		{"chain-2", 1, ts1},
	}
	for _, x := range vscSendTimestamps {
		legacySetVscSendTimestamp(store, x.chainId, x.vscId, x.ts)
	}

	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().UnbondingTime(ctx).Times(2),
	)

	unbondingPeriod, err := pk.UnbondingTime(ctx)
	require.NoError(t, err)

	err = MigrateConsumerAddrsToPrune(ctx, store, pk)
	require.NoError(t, err)

	consumerAddrs := pk.GetAllConsumerAddrsToPrune(ctx, "chain-1")
	require.Len(t, consumerAddrs, 3)
	// two addresses with ts1
	require.Equal(t, ts1.Add(unbondingPeriod).UTC(), consumerAddrs[0].PruneTs)
	require.Len(t, consumerAddrs[0].ConsumerAddrs.Addresses, 2)
	consumerAddr := providertypes.NewConsumerConsAddress(consumerAddrs[0].ConsumerAddrs.Addresses[0])
	require.Equal(t, consumerAddrsToPrune[0].address, consumerAddr)
	consumerAddr = providertypes.NewConsumerConsAddress(consumerAddrs[0].ConsumerAddrs.Addresses[1])
	require.Equal(t, consumerAddrsToPrune[1].address, consumerAddr)
	// one address with ts2
	require.Equal(t, ts2.Add(unbondingPeriod).UTC(), consumerAddrs[1].PruneTs)
	require.Len(t, consumerAddrs[1].ConsumerAddrs.Addresses, 1)
	consumerAddr = providertypes.NewConsumerConsAddress(consumerAddrs[1].ConsumerAddrs.Addresses[0])
	require.Equal(t, consumerAddrsToPrune[3].address, consumerAddr)
	// one address with ts3
	require.Equal(t, ts3.Add(unbondingPeriod).UTC(), consumerAddrs[2].PruneTs)
	require.Len(t, consumerAddrs[2].ConsumerAddrs.Addresses, 1)
	consumerAddr = providertypes.NewConsumerConsAddress(consumerAddrs[2].ConsumerAddrs.Addresses[0])
	require.Equal(t, consumerAddrsToPrune[4].address, consumerAddr)

	consumerAddrs = pk.GetAllConsumerAddrsToPrune(ctx, "chain-2")
	require.Len(t, consumerAddrs, 1)
	// one address with ts1
	require.Equal(t, ts1.Add(unbondingPeriod).UTC(), consumerAddrs[0].PruneTs)
	require.Len(t, consumerAddrs[0].ConsumerAddrs.Addresses, 1)
	consumerAddr = providertypes.NewConsumerConsAddress(consumerAddrs[0].ConsumerAddrs.Addresses[0])
	require.Equal(t, consumerAddrsToPrune[2].address, consumerAddr)

}
