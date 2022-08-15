package keeper

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	auth "github.com/cosmos/cosmos-sdk/x/auth/types"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibcexported "github.com/cosmos/ibc-go/v3/modules/core/exported"
	"github.com/stretchr/testify/mock"
	abci "github.com/tendermint/tendermint/abci/types"
)

// Defines the default mock implementations of various keepers referenced by the provider keeper.
// If any keeper method is called without an explicit statement that such a call is expected,
// the test will panic, see https://pkg.go.dev/github.com/stretchr/testify/mock#Mock.On
//
// Note: If you need to mock the behavior of specific keeper method(s) in a different
// way than the provided defaults, you can define a new mock implementation in another file.

type MockChannelKeeper struct {
	mock.Mock
}

func (m MockChannelKeeper) GetChannel(ctx sdk.Context, srcPort, srcChan string) (channel channeltypes.Channel, found bool) {
	m.Called(ctx, srcPort, srcChan)
	return channel, false
}
func (m MockChannelKeeper) GetNextSequenceSend(ctx sdk.Context, portID, channelID string) (uint64, bool) {
	m.Called(ctx, portID, channelID)
	return 0, false
}
func (m MockChannelKeeper) SendPacket(ctx sdk.Context, channelCap *capabilitytypes.Capability, packet ibcexported.PacketI) error {
	m.Called(ctx, channelCap, packet)
	return nil
}
func (m MockChannelKeeper) WriteAcknowledgement(ctx sdk.Context, chanCap *capabilitytypes.Capability, packet ibcexported.PacketI, acknowledgement ibcexported.Acknowledgement) error {
	m.Called(ctx, chanCap, packet, acknowledgement)
	return nil
}
func (m MockChannelKeeper) ChanCloseInit(ctx sdk.Context, portID, channelID string, chanCap *capabilitytypes.Capability) error {
	m.Called(ctx, portID, channelID, chanCap)
	return nil
}

type MockPortKeeper struct {
	mock.Mock
}

func (m MockPortKeeper) BindPort(ctx sdk.Context, portID string) *capabilitytypes.Capability {
	m.Called(ctx, portID)
	return &capabilitytypes.Capability{}
}

type MockConnectionKeeper struct {
	mock.Mock
}

func (m MockConnectionKeeper) GetConnection(ctx sdk.Context, connectionID string) (conntypes.ConnectionEnd, bool) {
	m.Called(ctx, connectionID)
	return conntypes.ConnectionEnd{}, false
}

type MockClientKeeper struct {
	mock.Mock
}

func (m MockClientKeeper) CreateClient(ctx sdk.Context, clientState ibcexported.ClientState, consensusState ibcexported.ConsensusState) (string, error) {
	m.Called(ctx, clientState, consensusState)
	return "", nil
}
func (m MockClientKeeper) GetClientState(ctx sdk.Context, clientID string) (ibcexported.ClientState, bool) {
	m.Called(ctx, clientID)
	return nil, false
}
func (m MockClientKeeper) GetLatestClientConsensusState(ctx sdk.Context, clientID string) (ibcexported.ConsensusState, bool) {
	m.Called(ctx, clientID)
	return nil, false
}
func (m MockClientKeeper) GetSelfConsensusState(ctx sdk.Context, height ibcexported.Height) (ibcexported.ConsensusState, error) {
	m.Called(ctx, height)
	return nil, nil
}

type MockStakingKeeper struct {
	mock.Mock
}

func (m MockStakingKeeper) GetValidatorUpdates(ctx sdk.Context) []abci.ValidatorUpdate {
	m.Called(ctx)
	return nil
}
func (m MockStakingKeeper) UnbondingCanComplete(ctx sdk.Context, id uint64) error {
	m.Called(ctx, id)
	return nil
}
func (m MockStakingKeeper) UnbondingTime(ctx sdk.Context) time.Duration {
	m.Called(ctx)
	return 0
}

// Returns a bonded validator with the given address
func (m MockStakingKeeper) GetValidatorByConsAddr(ctx sdk.Context, consAddr sdk.ConsAddress) (validator stakingtypes.Validator, found bool) {
	m.Called(ctx, consAddr)
	val := stakingtypes.Validator{
		Status: stakingtypes.Bonded,
	}
	return val, true
}
func (m MockStakingKeeper) Jail(ctx sdk.Context, addr sdk.ConsAddress) {
	m.Called(ctx, addr)
}
func (m MockStakingKeeper) Slash(ctx sdk.Context, addr sdk.ConsAddress,
	infractionHeight int64, power int64, slashFraction sdk.Dec, infraction stakingtypes.InfractionType) {
	m.Called(ctx, addr, infractionHeight, power, slashFraction, infraction)
}
func (m MockStakingKeeper) GetValidator(ctx sdk.Context, addr sdk.ValAddress) (validator stakingtypes.Validator, found bool) {
	return stakingtypes.Validator{}, false
}
func (m MockStakingKeeper) IterateLastValidatorPowers(ctx sdk.Context, cb func(addr sdk.ValAddress, power int64) (stop bool)) {
}
func (m MockStakingKeeper) PowerReduction(ctx sdk.Context) sdk.Int {
	return sdk.ZeroInt()
}
func (m MockStakingKeeper) PutUnbondingOnHold(ctx sdk.Context, id uint64) error {
	return nil
}

type MockSlashingKeeper struct {
	mock.Mock
}

func (m MockSlashingKeeper) JailUntil(ctx sdk.Context, addr sdk.ConsAddress, t time.Time) {
	m.Called(ctx, addr, t)
}
func (m MockSlashingKeeper) GetValidatorSigningInfo(ctx sdk.Context, address sdk.ConsAddress) (info slashingtypes.ValidatorSigningInfo, found bool) {
	m.Called(ctx, address)
	return slashingtypes.ValidatorSigningInfo{}, false
}
func (m MockSlashingKeeper) DowntimeJailDuration(ctx sdk.Context) time.Duration {
	m.Called(ctx)
	return 0
}
func (m MockSlashingKeeper) SlashFractionDowntime(ctx sdk.Context) sdk.Dec {
	m.Called(ctx)
	return sdk.Dec{}
}
func (m MockSlashingKeeper) SlashFractionDoubleSign(ctx sdk.Context) (res sdk.Dec) {
	m.Called(ctx)
	return sdk.NewDec(1)
}
func (m MockSlashingKeeper) Tombstone(ctx sdk.Context, addr sdk.ConsAddress) {
	m.Called(ctx, addr)
}
func (m MockSlashingKeeper) IsTombstoned(ctx sdk.Context, addr sdk.ConsAddress) bool {
	m.Called(ctx, addr)
	return false
}

type MockAccountKeeper struct {
	mock.Mock
}

func (m MockAccountKeeper) GetModuleAccount(ctx sdk.Context, name string) auth.ModuleAccountI {
	m.Called(ctx, name)
	return nil
}
