package v8

import (
	"cosmossdk.io/math"
	"encoding/binary"
	"fmt"
	"github.com/cometbft/cometbft/proto/tendermint/crypto"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/types"
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
	return providertypes.StringIdAndUintIdKey(LegacyConsumerAddrsToPruneBytePrefix, chainID, vscID)
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
	return providertypes.StringIdAndUintIdKey(LegacyVscSendTimestampBytePrefix, chainID, vscID)
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

// ChainData corresponds to some general data that a consumer chain states in store
type ChainData struct {
	ChainId           string
	ClientId          string
	ChannelId         string
	ConsumerGenesis   types.ConsumerGenesisState
	SlashAcks         []string
	InitChainHeight   uint64
	PendingVSCPackets []types.ValidatorSetChangePacketData
	// A chain could contain multiple validators and hence provider addresses and multiple
	// consumer keys and consumer addresses. For simplicity of testing here, we only consider a single
	// provider and consumer address and a single consumer key.
	ProviderAddr              providertypes.ProviderConsAddress
	ConsumerKey               crypto.PublicKey
	ConsumerAddr              providertypes.ConsumerConsAddress
	EquivocationMinHeight     uint64
	ConsensusValidator        providertypes.ConsensusValidator
	ConsumerRewardsAllocation providertypes.ConsumerRewardsAllocation
	ConsumerCommissionRate    math.LegacyDec
	MinimumPowerInTopN        int64
	PruneTs                   time.Time
	TopN                      uint32
	ValidatorsPowerCap        uint32
	ValidatorSetCap           uint32
}

func StoreChainDataUsingChainIdAsKey(ctx sdk.Context, store storetypes.KVStore, providerKeeper providerkeeper.Keeper, data ChainData) {
	providerKeeper.SetConsumerClientId(ctx, data.ChainId, data.ClientId)

	providerKeeper.SetConsumerIdToChannelId(ctx, data.ChainId, data.ChannelId)
	providerKeeper.SetChannelToConsumerId(ctx, data.ChannelId, data.ChainId)

	providerKeeper.SetConsumerGenesis(ctx, data.ChainId, data.ConsumerGenesis)

	providerKeeper.SetSlashAcks(ctx, data.ChainId, data.SlashAcks)

	providerKeeper.SetInitChainHeight(ctx, data.ChainId, data.InitChainHeight)

	for _, packet := range data.PendingVSCPackets {
		providerKeeper.AppendPendingVSCPackets(ctx, data.ChainId, packet)
	}

	providerKeeper.SetValidatorConsumerPubKey(ctx, data.ChainId, data.ProviderAddr, data.ConsumerKey)

	providerKeeper.SetValidatorByConsumerAddr(ctx, data.ChainId, data.ConsumerAddr, data.ProviderAddr)

	providerKeeper.SetEquivocationEvidenceMinHeight(ctx, data.ChainId, data.EquivocationMinHeight)

	providerKeeper.SetConsumerValidator(ctx, data.ChainId, data.ConsensusValidator)

	providerKeeper.SetOptedIn(ctx, data.ChainId, data.ProviderAddr)

	providerKeeper.SetAllowlist(ctx, data.ChainId, data.ProviderAddr)

	providerKeeper.SetDenylist(ctx, data.ChainId, data.ProviderAddr)

	providerKeeper.SetConsumerRewardsAllocation(ctx, data.ChainId, data.ConsumerRewardsAllocation)

	providerKeeper.SetConsumerCommissionRate(ctx, data.ChainId, data.ProviderAddr, data.ConsumerCommissionRate)

	providerKeeper.SetMinimumPowerInTopN(ctx, data.ChainId, data.MinimumPowerInTopN)

	providerKeeper.AppendConsumerAddrsToPrune(ctx, data.ChainId, data.PruneTs, data.ConsumerAddr)

	// set Top N
	topNKey := providertypes.StringIdWithLenKey(LegacyTopNKeyPrefix, data.ChainId)
	buf := make([]byte, 4)
	binary.BigEndian.PutUint32(buf, data.TopN)
	store.Set(topNKey, buf)

	// set validators power cap
	validatorsPowerCapKey := providertypes.StringIdWithLenKey(LegacyValidatorsPowerCapKeyPrefix, data.ChainId)
	buf = make([]byte, 4)
	binary.BigEndian.PutUint32(buf, data.ValidatorsPowerCap)
	store.Set(validatorsPowerCapKey, buf)

	// set validator set cap
	validatorSetCapKey := providertypes.StringIdWithLenKey(LegacyValidatorSetCapKeyPrefix, data.ChainId)
	buf = make([]byte, 4)
	binary.BigEndian.PutUint32(buf, data.ValidatorSetCap)
	store.Set(validatorSetCapKey, buf)
}

// GetChainDataUsingStringId retrieves the store data under key `id` that can be either a `chainId` or a `consumerId`.
// If `stopEarly` is set, the code will return an error if it finds an inconsistency in the retrieved chain data.
func GetChainDataUsingStringId(ctx sdk.Context, providerKeeper providerkeeper.Keeper, id string,
	providerAddr providertypes.ProviderConsAddress, consumerAddr providertypes.ConsumerConsAddress, stopEarly bool) (ChainData, error) {
	data := ChainData{}
	data.ChainId, _ = providerKeeper.GetConsumerChainId(ctx, id)
	data.ClientId, _ = providerKeeper.GetConsumerClientId(ctx, id)

	data.ChannelId, _ = providerKeeper.GetConsumerIdToChannelId(ctx, id)
	retrievedConsumerId, _ := providerKeeper.GetChannelIdToConsumerId(ctx, data.ChannelId)
	if stopEarly && id != retrievedConsumerId {
		return ChainData{},
			fmt.Errorf("retrieved consumer id (%s) should be (%s)", retrievedConsumerId, id)
	}

	data.ConsumerGenesis, _ = providerKeeper.GetConsumerGenesis(ctx, id)

	data.SlashAcks = providerKeeper.GetSlashAcks(ctx, id)

	data.InitChainHeight, _ = providerKeeper.GetInitChainHeight(ctx, id)

	pendingVSCPackets := providerKeeper.GetPendingVSCPackets(ctx, id)
	if len(pendingVSCPackets) > 0 {
		data.PendingVSCPackets = pendingVSCPackets
	}

	data.ConsumerKey, _ = providerKeeper.GetValidatorConsumerPubKey(ctx, id, providerAddr)

	data.ProviderAddr, _ = providerKeeper.GetValidatorByConsumerAddr(ctx, id, consumerAddr)
	if stopEarly && data.ProviderAddr.String() != providerAddr.String() {
		return ChainData{}, fmt.Errorf("retrieved providerAddr (%s) should be (%s)", data.ProviderAddr.String(), providerAddr.String())
	}

	data.EquivocationMinHeight = providerKeeper.GetEquivocationEvidenceMinHeight(ctx, id)

	data.ConsensusValidator, _ = providerKeeper.GetConsumerValidator(ctx, id, providerAddr)

	optedInValidators := providerKeeper.GetAllOptedIn(ctx, id)
	if len(optedInValidators) > 0 {
		tempProviderAddr := optedInValidators[0]
		if stopEarly && tempProviderAddr.String() != providerAddr.String() {
			return ChainData{}, fmt.Errorf("retrieved providerAddr (%s) should be (%s)", tempProviderAddr.String(), providerAddr.String())
		}
	}

	allowlist := providerKeeper.GetAllowList(ctx, id)
	if len(allowlist) > 0 {
		tempProviderAddr := allowlist[0]
		if stopEarly && tempProviderAddr.String() != providerAddr.String() {
			return ChainData{}, fmt.Errorf("retrieved providerAddr (%s) should be (%s)", tempProviderAddr.String(), providerAddr.String())
		}
	}

	denylist := providerKeeper.GetDenyList(ctx, id)
	if len(denylist) > 0 {
		tempProviderAddr := denylist[0]
		if stopEarly && tempProviderAddr.String() != providerAddr.String() {
			return ChainData{}, fmt.Errorf("retrieved providerAddr (%s) should be (%s)", tempProviderAddr.String(), providerAddr.String())
		}
	}

	data.ConsumerRewardsAllocation = providerKeeper.GetConsumerRewardsAllocation(ctx, id)

	consumerCommissionRate, found := providerKeeper.GetConsumerCommissionRate(ctx, id, providerAddr)
	if found {
		data.ConsumerCommissionRate = consumerCommissionRate
	}

	data.MinimumPowerInTopN, _ = providerKeeper.GetMinimumPowerInTopN(ctx, id)

	consumerAddressesToPruneV2 := providerKeeper.GetAllConsumerAddrsToPrune(ctx, id)
	if len(consumerAddressesToPruneV2) > 0 {
		consumerAddrToPruneV2 := consumerAddressesToPruneV2[0]
		consumerAddrToPrune := consumerAddrToPruneV2.ConsumerAddrs.Addresses[0]
		data.ConsumerAddr = providertypes.NewConsumerConsAddress(consumerAddrToPrune)
		if stopEarly && data.ConsumerAddr.String() != consumerAddr.String() {
			return ChainData{}, fmt.Errorf("retrieved consumerAddr (%s) should be (%s)", data.ConsumerAddr.String(), consumerAddr.String())
		}
		data.PruneTs = consumerAddrToPruneV2.PruneTs
	}

	powerShapingParameters, _ := providerKeeper.GetConsumerPowerShapingParameters(ctx, id)
	data.TopN = powerShapingParameters.Top_N
	data.ValidatorsPowerCap = powerShapingParameters.ValidatorsPowerCap
	data.ValidatorSetCap = powerShapingParameters.ValidatorSetCap

	return data, nil
}

func CreateTestChainData(chainId string, clientId string, channelId string) ChainData {
	return ChainData{
		ChainId:   chainId,
		ClientId:  clientId,
		ChannelId: channelId,
		ConsumerGenesis: types.ConsumerGenesisState{
			Params:   types.ConsumerParams{ConsumerRedistributionFraction: "redistribution fraction"},
			NewChain: true,
		},
		SlashAcks:                 []string{"slashAck1", "slashAck2"},
		InitChainHeight:           uint64(123),
		PendingVSCPackets:         []types.ValidatorSetChangePacketData{{ValsetUpdateId: uint64(456)}},
		ProviderAddr:              providertypes.NewProviderConsAddress([]byte("provider cons address")),
		ConsumerKey:               crypto.PublicKey{Sum: &crypto.PublicKey_Ed25519{Ed25519: []byte{4}}},
		ConsumerAddr:              providertypes.NewConsumerConsAddress([]byte("consumer cons address")),
		EquivocationMinHeight:     uint64(789),
		ConsensusValidator:        providertypes.ConsensusValidator{},
		ConsumerRewardsAllocation: providertypes.ConsumerRewardsAllocation{Rewards: sdk.NewDecCoins(sdk.NewDecCoin("uatom", math.NewInt(1000)))},
		ConsumerCommissionRate:    math.LegacyNewDec(1),
		MinimumPowerInTopN:        int64(123456789),
		PruneTs:                   time.Now().UTC(),
		TopN:                      uint32(67),
		ValidatorsPowerCap:        uint32(30),
		ValidatorSetCap:           uint32(100),
	}
}

func TestMigrateLaunchedConsumerChains(t *testing.T) {
	t.Helper()
	inMemParams := testutil.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	store := ctx.KVStore(inMemParams.StoreKey)

	// create two sample chains with chain data
	chainId1 := "chainId1"
	chainData1 := CreateTestChainData(chainId1, "clientId1", "channelId1")
	StoreChainDataUsingChainIdAsKey(ctx, store, providerKeeper, chainData1)

	chainId2 := "chainId2"
	chainData2 := CreateTestChainData(chainId2, "clientId2", "channelId2")
	StoreChainDataUsingChainIdAsKey(ctx, store, providerKeeper, chainData2)

	// migrate the launched chains
	err := MigrateLaunchedConsumerChains(ctx, store, providerKeeper)
	require.NoError(t, err)

	// assert that the launched chains do not reside under the `chainId` anymore
	providerAddr := chainData1.ProviderAddr
	consumerAddr := chainData2.ConsumerAddr
	oldChainData1, err := GetChainDataUsingStringId(ctx, providerKeeper, chainId1, providerAddr, consumerAddr, false)
	require.Equal(t, oldChainData1, ChainData{})

	oldChainData2, err := GetChainDataUsingStringId(ctx, providerKeeper, chainId2, providerAddr, consumerAddr, false)
	require.Equal(t, oldChainData2, ChainData{})

	// assert that the launched chains have been transferred to reside under a `consumerId`
	actualChainData1, err := GetChainDataUsingStringId(ctx, providerKeeper, "0", providerAddr, consumerAddr, true)
	require.NoError(t, err)
	require.Equal(t, chainData1, actualChainData1)

	actualChainData2, err := GetChainDataUsingStringId(ctx, providerKeeper, "1", providerAddr, consumerAddr, true)
	require.NoError(t, err)
	require.Equal(t, chainData2, actualChainData2)
}

func TestTransformConsAddressesToBech32Addresses(t *testing.T) {
	expectedBech32Addresses := []string{
		"cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
		"cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
		"cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
	}
	addresses := []providertypes.ProviderConsAddress{}
	for _, addr := range expectedBech32Addresses {
		ca, _ := sdk.ConsAddressFromBech32(addr)
		addresses = append(addresses, providertypes.NewProviderConsAddress(ca))
	}

	actualBech32Addresses := TransformConsAddressesToBech32Addresses(addresses)
	require.Equal(t, expectedBech32Addresses, actualBech32Addresses)
}

// TestCleanupState asserts that a subset of the cleaning up indeed takes place
func TestCleanupState(t *testing.T) {
	t.Helper()
	inMemParams := testutil.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	store := ctx.KVStore(inMemParams.StoreKey)

	containsData := func(prefix byte) bool {
		iterator := storetypes.KVStorePrefixIterator(store, []byte{prefix})
		defer iterator.Close()

		return iterator.Valid()
	}

	// create two sample chains with chain data
	chainId1 := "chainId1"
	chainData1 := CreateTestChainData(chainId1, "clientId1", "channelId1")
	StoreChainDataUsingChainIdAsKey(ctx, store, providerKeeper, chainData1)
	require.True(t, containsData(LegacyTopNKeyPrefix))
	require.True(t, containsData(LegacyValidatorsPowerCapKeyPrefix))
	require.True(t, containsData(LegacyValidatorSetCapKeyPrefix))

	CleanupState(store)
	require.False(t, containsData(LegacyTopNKeyPrefix))
	require.False(t, containsData(LegacyValidatorsPowerCapKeyPrefix))
	require.False(t, containsData(LegacyValidatorSetCapKeyPrefix))
}
