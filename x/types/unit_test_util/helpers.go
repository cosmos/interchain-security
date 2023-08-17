package ututil

import (
	"crypto/rand"
	"encoding/binary"
	"testing"

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
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmdb "github.com/cometbft/cometbft-db"
	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/libs/log"
	tmproto "github.com/cometbft/cometbft/proto/tendermint/types"

	"github.com/cosmos/interchain-security/x/types"
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
	*MockEvidenceKeeper
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
		MockEvidenceKeeper:     NewMockEvidenceKeeper(ctrl),
		MockDistributionKeeper: NewMockDistributionKeeper(ctrl),
	}
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
