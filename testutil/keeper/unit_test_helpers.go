package keeper

import (
	"crypto/rand"
	"encoding/binary"
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	"github.com/cosmos/cosmos-sdk/store"
	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmdb "github.com/cometbft/cometbft-db"
	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/libs/log"
	tmproto "github.com/cometbft/cometbft/proto/tendermint/types"

	consumerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// Parameters needed to instantiate an in-memory keeper
type InMemKeeperParams struct {
	Cdc            *codec.ProtoCodec
	StoreKey       *storetypes.KVStoreKey
	ParamsSubspace *paramstypes.Subspace
	Ctx            sdk.Context
}

// NewInMemKeeperParams instantiates in-memory keeper params with default values
func NewInMemKeeperParams(tb testing.TB) InMemKeeperParams {
	tb.Helper()
	storeKey := sdk.NewKVStoreKey(types.StoreKey)
	memStoreKey := storetypes.NewMemoryStoreKey(types.MemStoreKey)

	db := tmdb.NewMemDB()
	stateStore := store.NewCommitMultiStore(db)
	stateStore.MountStoreWithDB(storeKey, storetypes.StoreTypeIAVL, db)
	stateStore.MountStoreWithDB(memStoreKey, storetypes.StoreTypeMemory, nil)
	require.NoError(tb, stateStore.LoadLatestVersion())

	registry := codectypes.NewInterfaceRegistry()
	cryptocodec.RegisterInterfaces(registry) // Public key implementation registered here
	cdc := codec.NewProtoCodec(registry)

	paramsSubspace := paramstypes.NewSubspace(cdc,
		codec.NewLegacyAmino(),
		storeKey,
		memStoreKey,
		paramstypes.ModuleName,
	)
	ctx := sdk.NewContext(stateStore, tmproto.Header{}, false, log.NewNopLogger())

	return InMemKeeperParams{
		Cdc:            cdc,
		StoreKey:       storeKey,
		ParamsSubspace: &paramsSubspace,
		Ctx:            ctx,
	}
}

// A struct holding pointers to any mocked external keeper needed for provider/consumer keeper setup.
type MockedKeepers struct {
	*MockScopedKeeper
	*MockChannelKeeper
	*MockPortKeeper
	*MockConnectionKeeper
	*MockClientKeeper
	*MockStakingKeeper
	*MockSlashingKeeper
	*MockAccountKeeper
	*MockBankKeeper
	*MockIBCTransferKeeper
	*MockIBCCoreKeeper
	*MockDistributionKeeper
}

// NewMockedKeepers instantiates a struct with pointers to properly instantiated mocked keepers.
func NewMockedKeepers(ctrl *gomock.Controller) MockedKeepers {
	return MockedKeepers{
		MockScopedKeeper:       NewMockScopedKeeper(ctrl),
		MockChannelKeeper:      NewMockChannelKeeper(ctrl),
		MockPortKeeper:         NewMockPortKeeper(ctrl),
		MockConnectionKeeper:   NewMockConnectionKeeper(ctrl),
		MockClientKeeper:       NewMockClientKeeper(ctrl),
		MockStakingKeeper:      NewMockStakingKeeper(ctrl),
		MockSlashingKeeper:     NewMockSlashingKeeper(ctrl),
		MockAccountKeeper:      NewMockAccountKeeper(ctrl),
		MockBankKeeper:         NewMockBankKeeper(ctrl),
		MockIBCTransferKeeper:  NewMockIBCTransferKeeper(ctrl),
		MockIBCCoreKeeper:      NewMockIBCCoreKeeper(ctrl),
		MockDistributionKeeper: NewMockDistributionKeeper(ctrl),
	}
}

// NewInMemProviderKeeper instantiates an in-mem provider keeper from params and mocked keepers
func NewInMemProviderKeeper(params InMemKeeperParams, mocks MockedKeepers) providerkeeper.Keeper {
	return providerkeeper.NewKeeper(
		params.Cdc,
		params.StoreKey,
		*params.ParamsSubspace,
		mocks.MockScopedKeeper,
		mocks.MockChannelKeeper,
		mocks.MockPortKeeper,
		mocks.MockConnectionKeeper,
		mocks.MockClientKeeper,
		mocks.MockStakingKeeper,
		mocks.MockSlashingKeeper,
		mocks.MockAccountKeeper,
		mocks.MockDistributionKeeper,
		mocks.MockBankKeeper,
		authtypes.FeeCollectorName,
	)
}

// NewInMemConsumerKeeper instantiates an in-mem consumer keeper from params and mocked keepers
func NewInMemConsumerKeeper(params InMemKeeperParams, mocks MockedKeepers) consumerkeeper.Keeper {
	return consumerkeeper.NewKeeper(
		params.Cdc,
		params.StoreKey,
		*params.ParamsSubspace,
		mocks.MockScopedKeeper,
		mocks.MockChannelKeeper,
		mocks.MockPortKeeper,
		mocks.MockConnectionKeeper,
		mocks.MockClientKeeper,
		mocks.MockSlashingKeeper,
		mocks.MockBankKeeper,
		mocks.MockAccountKeeper,
		mocks.MockIBCTransferKeeper,
		mocks.MockIBCCoreKeeper,
		authtypes.FeeCollectorName,
	)
}

// Returns an in-memory provider keeper, context, controller, and mocks, given a test instance and parameters.
//
// Note: Calling ctrl.Finish() at the end of a test function ensures that
// no unexpected calls to external keepers are made.
func GetProviderKeeperAndCtx(t *testing.T, params InMemKeeperParams) (
	providerkeeper.Keeper, sdk.Context, *gomock.Controller, MockedKeepers,
) {
	t.Helper()
	ctrl := gomock.NewController(t)
	mocks := NewMockedKeepers(ctrl)
	return NewInMemProviderKeeper(params, mocks), params.Ctx, ctrl, mocks
}

// Return an in-memory consumer keeper, context, controller, and mocks, given a test instance and parameters.
//
// Note: Calling ctrl.Finish() at the end of a test function ensures that
// no unexpected calls to external keepers are made.
func GetConsumerKeeperAndCtx(t *testing.T, params InMemKeeperParams) (
	consumerkeeper.Keeper, sdk.Context, *gomock.Controller, MockedKeepers,
) {
	t.Helper()
	ctrl := gomock.NewController(t)
	mocks := NewMockedKeepers(ctrl)
	return NewInMemConsumerKeeper(params, mocks), params.Ctx, ctrl, mocks
}

type PrivateKey struct {
	PrivKey cryptotypes.PrivKey
}

// Obtains slash packet data with a newly generated key, and randomized field values
func GetNewSlashPacketData() types.SlashPacketData {
	b1 := make([]byte, 8)
	_, _ = rand.Read(b1)
	b2 := make([]byte, 8)
	_, _ = rand.Read(b2)
	b3 := make([]byte, 8)
	_, _ = rand.Read(b3)
	return types.SlashPacketData{
		Validator: abci.Validator{
			Address: ed25519.GenPrivKey().PubKey().Address(),
			Power:   int64(binary.BigEndian.Uint64(b1)),
		},
		ValsetUpdateId: binary.BigEndian.Uint64(b2),
		Infraction:     stakingtypes.Infraction(binary.BigEndian.Uint64(b2) % 3),
	}
}

// Obtains vsc matured packet data with a newly generated key
func GetNewVSCMaturedPacketData() types.VSCMaturedPacketData {
	b := make([]byte, 8)
	_, _ = rand.Read(b)
	return types.VSCMaturedPacketData{ValsetUpdateId: binary.BigEndian.Uint64(b)}
}

// SetupForStoppingConsumerChain registers expected mock calls and corresponding state setup
// which assert that a consumer chain was properly setup to be later stopped from `StopConsumerChain`.
// Note: This function only setups and tests that we correctly setup a consumer chain that we could later stop when
// calling `StopConsumerChain` -- this does NOT necessarily mean that the consumer chain is stopped.
// Also see `TestProviderStateIsCleanedAfterConsumerChainIsStopped`.
func SetupForStoppingConsumerChain(t *testing.T, ctx sdk.Context,
	providerKeeper *providerkeeper.Keeper, mocks MockedKeepers,
) {
	t.Helper()
	expectations := GetMocksForCreateConsumerClient(ctx, &mocks,
		"chainID", clienttypes.NewHeight(4, 5))
	expectations = append(expectations, GetMocksForSetConsumerChain(ctx, &mocks, "chainID")...)

	gomock.InOrder(expectations...)

	prop := GetTestConsumerAdditionProp()
	err := providerKeeper.CreateConsumerClient(ctx, prop)
	require.NoError(t, err)
	err = providerKeeper.SetConsumerChain(ctx, "channelID")
	require.NoError(t, err)
}

// TestProviderStateIsCleanedAfterConsumerChainIsStopped executes test assertions for the provider's state being cleaned
// after a stopped consumer chain.
func TestProviderStateIsCleanedAfterConsumerChainIsStopped(t *testing.T, ctx sdk.Context, providerKeeper providerkeeper.Keeper,
	expectedChainID, expectedChannelID string,
) {
	t.Helper()
	_, found := providerKeeper.GetConsumerClientId(ctx, expectedChainID)
	require.False(t, found)
	_, found = providerKeeper.GetChainToChannel(ctx, expectedChainID)
	require.False(t, found)
	_, found = providerKeeper.GetChannelToChain(ctx, expectedChannelID)
	require.False(t, found)
	_, found = providerKeeper.GetInitChainHeight(ctx, expectedChainID)
	require.False(t, found)
	acks := providerKeeper.GetSlashAcks(ctx, expectedChainID)
	require.Empty(t, acks)
	_, found = providerKeeper.GetInitTimeoutTimestamp(ctx, expectedChainID)
	require.False(t, found)

	require.Empty(t, providerKeeper.GetAllVscSendTimestamps(ctx, expectedChainID))

	// test key assignment state is cleaned
	require.Empty(t, providerKeeper.GetAllValidatorConsumerPubKeys(ctx, &expectedChainID))
	require.Empty(t, providerKeeper.GetAllValidatorsByConsumerAddr(ctx, &expectedChainID))
	require.Empty(t, providerKeeper.GetAllKeyAssignmentReplacements(ctx, expectedChainID))
	require.Empty(t, providerKeeper.GetAllConsumerAddrsToPrune(ctx, expectedChainID))

	allGlobalEntries := providerKeeper.GetAllGlobalSlashEntries(ctx)
	for _, entry := range allGlobalEntries {
		require.NotEqual(t, expectedChainID, entry.ConsumerChainID)
	}

	slashPacketData, vscMaturedPacketData, _, _ := providerKeeper.GetAllThrottledPacketData(ctx, expectedChainID)
	require.Empty(t, slashPacketData)
	require.Empty(t, vscMaturedPacketData)
}

func GetTestConsumerAdditionProp() *providertypes.ConsumerAdditionProposal {
	prop := providertypes.NewConsumerAdditionProposal(
		"chainID",
		"description",
		"chainID",
		clienttypes.NewHeight(4, 5),
		[]byte("gen_hash"),
		[]byte("bin_hash"),
		time.Now(),
		types.DefaultConsumerRedistributeFrac,
		types.DefaultBlocksPerDistributionTransmission,
		"",
		types.DefaultHistoricalEntries,
		types.DefaultCCVTimeoutPeriod,
		types.DefaultTransferTimeoutPeriod,
		types.DefaultConsumerUnbondingPeriod,
	).(*providertypes.ConsumerAdditionProposal)

	return prop
}

// Obtains a CrossChainValidator with a newly generated key, and randomized field values
func GetNewCrossChainValidator(t *testing.T) consumertypes.CrossChainValidator {
	t.Helper()
	b1 := make([]byte, 8)
	_, _ = rand.Read(b1)
	power := int64(binary.BigEndian.Uint64(b1))
	privKey := ed25519.GenPrivKey()
	validator, err := consumertypes.NewCCValidator(privKey.PubKey().Address(), power, privKey.PubKey())
	require.NoError(t, err)
	return validator
}
