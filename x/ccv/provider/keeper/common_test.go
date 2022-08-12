package keeper_test

import (
	"testing"
	"time"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/store"
	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	auth "github.com/cosmos/cosmos-sdk/x/auth/types"
	capabilitykeeper "github.com/cosmos/cosmos-sdk/x/capability/keeper"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibcexported "github.com/cosmos/ibc-go/v3/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	"github.com/tendermint/tendermint/libs/log"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmdb "github.com/tendermint/tm-db"
)

// Constructs a keeper and context object for unit tests, backed by an in-memory db.
func getKeeperAndCtx(t testing.TB) (keeper.Keeper, sdk.Context) {

	cdc, storeKey, paramsSubspace, stateStore := setupInMemKeeper(t)

	k := keeper.NewKeeper(
		cdc,
		storeKey,
		paramsSubspace,
		capabilitykeeper.ScopedKeeper{},
		DummyChannelKeeper{},
		DummyPortKeeper{},
		DummyConnectionKeeper{},
		DummyClientKeeper{},
		DummyStakingKeeper{},
		DummySlashingKeeper{},
		DummyAccountKeeper{},
		"",
	)
	ctx := sdk.NewContext(stateStore, tmproto.Header{}, false, log.NewNopLogger())
	return k, ctx
}

// Constructs a keeper and context object for unit tests, backed by an in-memory db, with ability to pass mocked keepers.
// Note: Use the dummy types defined in this file for keepers you don't wish to mock.
func getKeeperAndCtxWithMocks(t testing.TB,
	capabilityKeeper capabilitykeeper.ScopedKeeper,
	channelKeeper types.ChannelKeeper,
	portKeeper types.PortKeeper,
	connectionKeeper types.ConnectionKeeper,
	clientKeeper types.ClientKeeper,
	stakingKeeper types.StakingKeeper,
	slashingKeeper types.SlashingKeeper,
	accountKeeper types.AccountKeeper,
) (keeper.Keeper, sdk.Context) {

	cdc, storeKey, paramsSubspace, stateStore := setupInMemKeeper(t)

	k := keeper.NewKeeper(
		cdc,
		storeKey,
		paramsSubspace,
		capabilityKeeper,
		channelKeeper,
		portKeeper,
		connectionKeeper,
		clientKeeper,
		stakingKeeper,
		slashingKeeper,
		accountKeeper,
		"",
	)
	ctx := sdk.NewContext(stateStore, tmproto.Header{}, false, log.NewNopLogger())
	return k, ctx
}

func setupInMemKeeper(t testing.TB) (*codec.ProtoCodec, *storetypes.KVStoreKey, paramstypes.Subspace, storetypes.CommitMultiStore) {
	storeKey := sdk.NewKVStoreKey(types.StoreKey)
	memStoreKey := storetypes.NewMemoryStoreKey(types.MemStoreKey)

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
	return cdc, storeKey, paramsSubspace, stateStore
}

type DummyChannelKeeper struct{}

func (DummyChannelKeeper) GetChannel(ctx sdk.Context, srcPort, srcChan string) (channel channeltypes.Channel, found bool) {
	return channel, found
}
func (DummyChannelKeeper) GetNextSequenceSend(ctx sdk.Context, portID, channelID string) (uint64, bool) {
	return 0, false
}
func (DummyChannelKeeper) SendPacket(ctx sdk.Context, channelCap *capabilitytypes.Capability, packet ibcexported.PacketI) error {
	return nil
}
func (DummyChannelKeeper) WriteAcknowledgement(ctx sdk.Context, chanCap *capabilitytypes.Capability, packet ibcexported.PacketI, acknowledgement ibcexported.Acknowledgement) error {
	return nil
}
func (DummyChannelKeeper) ChanCloseInit(ctx sdk.Context, portID, channelID string, chanCap *capabilitytypes.Capability) error {
	return nil
}

type DummyPortKeeper struct{}

func (DummyPortKeeper) BindPort(ctx sdk.Context, portID string) *capabilitytypes.Capability {
	return &capabilitytypes.Capability{}
}

type DummyConnectionKeeper struct{}

func (DummyConnectionKeeper) GetConnection(ctx sdk.Context, connectionID string) (conntypes.ConnectionEnd, bool) {
	return conntypes.ConnectionEnd{}, false
}

type DummyClientKeeper struct{}

func (d DummyClientKeeper) CreateClient(ctx sdk.Context, clientState ibcexported.ClientState, consensusState ibcexported.ConsensusState) (string, error) {
	return "", nil
}
func (d DummyClientKeeper) GetClientState(ctx sdk.Context, clientID string) (ibcexported.ClientState, bool) {
	return nil, false
}
func (d DummyClientKeeper) GetLatestClientConsensusState(ctx sdk.Context, clientID string) (ibcexported.ConsensusState, bool) {
	return nil, false
}
func (d DummyClientKeeper) GetSelfConsensusState(ctx sdk.Context, height ibcexported.Height) (ibcexported.ConsensusState, error) {
	return nil, nil
}

type DummyStakingKeeper struct{}

func (m DummyStakingKeeper) GetValidatorUpdates(ctx sdk.Context) []abci.ValidatorUpdate {
	return nil
}
func (m DummyStakingKeeper) UnbondingCanComplete(ctx sdk.Context, id uint64) error {
	return nil
}
func (m DummyStakingKeeper) UnbondingTime(ctx sdk.Context) time.Duration {
	return 0
}
func (m DummyStakingKeeper) GetValidatorByConsAddr(ctx sdk.Context, consAddr sdk.ConsAddress) (validator stakingtypes.Validator, found bool) {
	return stakingtypes.Validator{}, false
}
func (m DummyStakingKeeper) Jail(sdk.Context, sdk.ConsAddress) {
}
func (m DummyStakingKeeper) Slash(sdk.Context, sdk.ConsAddress, int64, int64, sdk.Dec, stakingtypes.InfractionType) {
}
func (m DummyStakingKeeper) GetValidator(ctx sdk.Context, addr sdk.ValAddress) (validator stakingtypes.Validator, found bool) {
	return stakingtypes.Validator{}, false
}
func (m DummyStakingKeeper) IterateLastValidatorPowers(ctx sdk.Context, cb func(addr sdk.ValAddress, power int64) (stop bool)) {
}
func (m DummyStakingKeeper) PowerReduction(ctx sdk.Context) sdk.Int {
	return sdk.ZeroInt()
}
func (m DummyStakingKeeper) PutUnbondingOnHold(ctx sdk.Context, id uint64) error {
	return nil
}

type DummySlashingKeeper struct{}

func (d DummySlashingKeeper) JailUntil(sdk.Context, sdk.ConsAddress, time.Time) {}
func (d DummySlashingKeeper) GetValidatorSigningInfo(ctx sdk.Context, address sdk.ConsAddress) (info slashingtypes.ValidatorSigningInfo, found bool) {
	return slashingtypes.ValidatorSigningInfo{}, false
}
func (d DummySlashingKeeper) DowntimeJailDuration(sdk.Context) time.Duration {
	return 0
}
func (d DummySlashingKeeper) SlashFractionDowntime(sdk.Context) sdk.Dec {
	return sdk.Dec{}
}
func (d DummySlashingKeeper) SlashFractionDoubleSign(ctx sdk.Context) (res sdk.Dec) {
	return res
}
func (d DummySlashingKeeper) Tombstone(sdk.Context, sdk.ConsAddress) {}
func (d DummySlashingKeeper) IsTombstoned(sdk.Context, sdk.ConsAddress) bool {
	return false
}

type DummyAccountKeeper struct{}

func (d DummyAccountKeeper) GetModuleAccount(ctx sdk.Context, name string) auth.ModuleAccountI {
	return nil
}
