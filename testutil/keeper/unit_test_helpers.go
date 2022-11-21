package keeper

import (
	"math/rand"
	"testing"
	time "time"

	abci "github.com/tendermint/tendermint/abci/types"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/store"
	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/tendermint/crypto"
	"github.com/tendermint/tendermint/libs/log"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmdb "github.com/tendermint/tm-db"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
)

// Parameters needed to instantiate an in-memory keeper
type InMemKeeperParams struct {
	Cdc            *codec.ProtoCodec
	StoreKey       *storetypes.KVStoreKey
	ParamsSubspace *paramstypes.Subspace
	Ctx            sdk.Context
}

// NewInMemKeeperParams instantiates in-memory keeper params with default values
func NewInMemKeeperParams(t testing.TB) InMemKeeperParams {
	storeKey := sdk.NewKVStoreKey(ccvtypes.StoreKey)
	memStoreKey := storetypes.NewMemoryStoreKey(ccvtypes.MemStoreKey)

	db := tmdb.NewMemDB()
	stateStore := store.NewCommitMultiStore(db)
	stateStore.MountStoreWithDB(storeKey, sdk.StoreTypeIAVL, db)
	stateStore.MountStoreWithDB(memStoreKey, sdk.StoreTypeMemory, nil)
	require.NoError(t, stateStore.LoadLatestVersion())

	registry := codectypes.NewInterfaceRegistry()
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
}

// NewMockedKeepers instantiates a struct with pointers to properly instantiated mocked keepers.
func NewMockedKeepers(ctrl *gomock.Controller) MockedKeepers {
	return MockedKeepers{
		MockScopedKeeper:      NewMockScopedKeeper(ctrl),
		MockChannelKeeper:     NewMockChannelKeeper(ctrl),
		MockPortKeeper:        NewMockPortKeeper(ctrl),
		MockConnectionKeeper:  NewMockConnectionKeeper(ctrl),
		MockClientKeeper:      NewMockClientKeeper(ctrl),
		MockStakingKeeper:     NewMockStakingKeeper(ctrl),
		MockSlashingKeeper:    NewMockSlashingKeeper(ctrl),
		MockAccountKeeper:     NewMockAccountKeeper(ctrl),
		MockBankKeeper:        NewMockBankKeeper(ctrl),
		MockIBCTransferKeeper: NewMockIBCTransferKeeper(ctrl),
		MockIBCCoreKeeper:     NewMockIBCCoreKeeper(ctrl),
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
		"",
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
		"",
	)
}

// Returns an in-memory provider keeper, context, controller, and mocks, given a test instance and parameters.
//
// Note: Calling ctrl.Finish() at the end of a test function ensures that
// no unexpected calls to external keepers are made.
func GetProviderKeeperAndCtx(t *testing.T, params InMemKeeperParams) (
	providerkeeper.Keeper, sdk.Context, *gomock.Controller, MockedKeepers) {

	ctrl := gomock.NewController(t)
	mocks := NewMockedKeepers(ctrl)
	return NewInMemProviderKeeper(params, mocks), params.Ctx, ctrl, mocks
}

// Return an in-memory consumer keeper, context, controller, and mocks, given a test instance and parameters.
//
// Note: Calling ctrl.Finish() at the end of a test function ensures that
// no unexpected calls to external keepers are made.
func GetConsumerKeeperAndCtx(t *testing.T, params InMemKeeperParams) (
	consumerkeeper.Keeper, sdk.Context, *gomock.Controller, MockedKeepers) {

	ctrl := gomock.NewController(t)
	mocks := NewMockedKeepers(ctrl)
	return NewInMemConsumerKeeper(params, mocks), params.Ctx, ctrl, mocks
}

// Registers proto interfaces for params.Cdc
//
// For now, we explicitly force certain unit tests to register sdk crypto interfaces.
// TODO: This function will be executed automatically once https://github.com/cosmos/interchain-security/issues/273 is solved.
func (params *InMemKeeperParams) RegisterSdkCryptoCodecInterfaces() {
	ir := codectypes.NewInterfaceRegistry()
	// Public key implementation registered here
	cryptocodec.RegisterInterfaces(ir)
	// Replace default cdc, with a custom (registered) codec
	params.Cdc = codec.NewProtoCodec(ir)
}

type PrivateKey struct {
	PrivKey cryptotypes.PrivKey
}

// Generates a public key for unit tests (abiding by tricky interface implementations from tm/sdk)
func GenPubKey() (crypto.PubKey, error) {
	privKey := PrivateKey{ed25519.GenPrivKey()}
	return cryptocodec.ToTmPubKeyInterface(privKey.PrivKey.PubKey())
}

// Obtains slash packet data with a newly generated key
func GetNewSlashPacketData() ccvtypes.SlashPacketData {
	rand.Seed(time.Now().UnixNano())
	return ccvtypes.SlashPacketData{
		Validator: abci.Validator{
			Address: ed25519.GenPrivKey().PubKey().Address(),
			Power:   rand.Int63(),
		},
		ValsetUpdateId: rand.Uint64(),
		Infraction:     stakingtypes.InfractionType(rand.Intn(3)),
	}
}

// Obtains vsc matured packet data with a newly generated key
func GetNewVSCMaturedPacketData() ccvtypes.VSCMaturedPacketData {
	rand.Seed(time.Now().UnixNano())
	return ccvtypes.VSCMaturedPacketData{ValsetUpdateId: rand.Uint64()}
}

// SetupForStoppingConsumerChain registers expected mock calls and corresponding state setup
// which asserts that a consumer chain was properly stopped from StopConsumerChain().
func SetupForStoppingConsumerChain(t *testing.T, ctx sdk.Context,
	providerKeeper *providerkeeper.Keeper, mocks MockedKeepers) {

	expectations := GetMocksForCreateConsumerClient(ctx, &mocks,
		"chainID", clienttypes.NewHeight(2, 3))
	expectations = append(expectations, GetMocksForSetConsumerChain(ctx, &mocks, "chainID")...)
	expectations = append(expectations, GetMocksForStopConsumerChain(ctx, &mocks)...)

	gomock.InOrder(expectations...)

	err := providerKeeper.CreateConsumerClient(ctx, "chainID", clienttypes.NewHeight(2, 3), false)
	require.NoError(t, err)
	err = providerKeeper.SetConsumerChain(ctx, "channelID")
	require.NoError(t, err)
}
