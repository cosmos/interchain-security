package keeper

import (
	"encoding/binary"
	"fmt"
	"reflect"
	"time"

	"github.com/cosmos/cosmos-sdk/codec"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v4/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v4/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v4/modules/core/24-host"

	sdk "github.com/cosmos/cosmos-sdk/types"
	ccv "github.com/cosmos/interchain-security/core"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	tmtypes "github.com/tendermint/tendermint/abci/types"
	"github.com/tendermint/tendermint/libs/log"
)

// Keeper defines the Cross-Chain Validation Consumer Keeper
type Keeper struct {
	storeKey         sdk.StoreKey
	cdc              codec.BinaryCodec
	paramStore       paramtypes.Subspace
	scopedKeeper     ccv.ScopedKeeper
	channelKeeper    ccv.ChannelKeeper
	portKeeper       ccv.PortKeeper
	connectionKeeper ccv.ConnectionKeeper
	clientKeeper     ccv.ClientKeeper
	// standaloneStakingKeeper is the staking keeper that managed proof of stake for a previously standalone chain,
	// before the chain went through a standalone to consumer changeover.
	// This keeper is not used for consumers that launched with ICS, and is therefore set after the constructor.
	standaloneStakingKeeper ccv.StakingKeeper
	slashingKeeper          ccv.SlashingKeeper
	hooks                   ccv.ConsumerHooks
	bankKeeper              ccv.BankKeeper
	authKeeper              ccv.AccountKeeper
	ibcTransferKeeper       ccv.IBCTransferKeeper
	ibcCoreKeeper           ccv.IBCCoreKeeper
	feeCollectorName        string
}

// NewKeeper creates a new Consumer Keeper instance
// NOTE: the feeCollectorName is in reference to the consumer-chain fee
// collector (and not the provider chain)
func NewKeeper(
	cdc codec.BinaryCodec, key sdk.StoreKey, paramSpace paramtypes.Subspace,
	scopedKeeper ccv.ScopedKeeper,
	channelKeeper ccv.ChannelKeeper, portKeeper ccv.PortKeeper,
	connectionKeeper ccv.ConnectionKeeper, clientKeeper ccv.ClientKeeper,
	slashingKeeper ccv.SlashingKeeper, bankKeeper ccv.BankKeeper, accountKeeper ccv.AccountKeeper,
	ibcTransferKeeper ccv.IBCTransferKeeper, ibcCoreKeeper ccv.IBCCoreKeeper,
	feeCollectorName string,
) Keeper {
	// set KeyTable if it has not already been set
	if !paramSpace.HasKeyTable() {
		paramSpace = paramSpace.WithKeyTable(ccv.ConsumerParamKeyTable())
	}

	k := Keeper{
		storeKey:                key,
		cdc:                     cdc,
		paramStore:              paramSpace,
		scopedKeeper:            scopedKeeper,
		channelKeeper:           channelKeeper,
		portKeeper:              portKeeper,
		connectionKeeper:        connectionKeeper,
		clientKeeper:            clientKeeper,
		slashingKeeper:          slashingKeeper,
		bankKeeper:              bankKeeper,
		authKeeper:              accountKeeper,
		ibcTransferKeeper:       ibcTransferKeeper,
		ibcCoreKeeper:           ibcCoreKeeper,
		feeCollectorName:        feeCollectorName,
		standaloneStakingKeeper: nil,
	}

	k.mustValidateFields()
	return k
}

// SetStandaloneStakingKeeper sets the standalone staking keeper for the consumer chain.
// This method should only be called for previously standalone chains that are now consumers.
func (k *Keeper) SetStandaloneStakingKeeper(sk ccv.StakingKeeper) {
	k.standaloneStakingKeeper = sk
}

// Validates that the consumer keeper is initialized with non-zero and
// non-nil values for all its fields. Otherwise this method will panic.
func (k Keeper) mustValidateFields() {
	// Ensures no fields are missed in this validation
	if reflect.ValueOf(k).NumField() != 16 {
		panic("number of fields in consumer keeper is not 16")
	}

	// Note 14 / 16 fields will be validated,
	// hooks are explicitly set after the constructor,
	// stakingKeeper is optionally set after the constructor,

	ccv.PanicIfZeroOrNil(k.storeKey, "storeKey")                   // 1
	ccv.PanicIfZeroOrNil(k.cdc, "cdc")                             // 2
	ccv.PanicIfZeroOrNil(k.paramStore, "paramStore")               // 3
	ccv.PanicIfZeroOrNil(k.scopedKeeper, "scopedKeeper")           // 4
	ccv.PanicIfZeroOrNil(k.channelKeeper, "channelKeeper")         // 5
	ccv.PanicIfZeroOrNil(k.portKeeper, "portKeeper")               // 6
	ccv.PanicIfZeroOrNil(k.connectionKeeper, "connectionKeeper")   // 7
	ccv.PanicIfZeroOrNil(k.clientKeeper, "clientKeeper")           // 8
	ccv.PanicIfZeroOrNil(k.slashingKeeper, "slashingKeeper")       // 9
	ccv.PanicIfZeroOrNil(k.bankKeeper, "bankKeeper")               // 10
	ccv.PanicIfZeroOrNil(k.authKeeper, "authKeeper")               // 11
	ccv.PanicIfZeroOrNil(k.ibcTransferKeeper, "ibcTransferKeeper") // 12
	ccv.PanicIfZeroOrNil(k.ibcCoreKeeper, "ibcCoreKeeper")         // 13
	ccv.PanicIfZeroOrNil(k.feeCollectorName, "feeCollectorName")   // 14
}

// Logger returns a module-specific logger.
func (k Keeper) Logger(ctx sdk.Context) log.Logger {
	return ctx.Logger().With("module", "x/"+host.ModuleName+"-"+types.ModuleName)
}

func (k *Keeper) SetHooks(sh ccv.ConsumerHooks) *Keeper {
	if k.hooks != nil {
		// This should never happen as SetHooks is expected
		// to be called only once in app.go
		panic("cannot set validator hooks twice")
	}

	k.hooks = sh

	return k
}

// ChanCloseInit defines a wrapper function for the channel Keeper's function
// Following ICS 004: https://github.com/cosmos/ibc/tree/main/spec/core/ics-004-channel-and-packet-semantics#closing-handshake
func (k Keeper) ChanCloseInit(ctx sdk.Context, portID, channelID string) error {
	capName := host.ChannelCapabilityPath(portID, channelID)
	chanCap, ok := k.scopedKeeper.GetCapability(ctx, capName)
	if !ok {
		return sdkerrors.Wrapf(channeltypes.ErrChannelCapabilityNotFound, "could not retrieve channel capability at: %s", capName)
	}
	return k.channelKeeper.ChanCloseInit(ctx, portID, channelID, chanCap)
}

// IsBound checks if the transfer module is already bound to the desired port
func (k Keeper) IsBound(ctx sdk.Context, portID string) bool {
	_, ok := k.scopedKeeper.GetCapability(ctx, host.PortPath(portID))
	return ok
}

// BindPort defines a wrapper function for the ort Keeper's function in
// order to expose it to module's InitGenesis function
func (k Keeper) BindPort(ctx sdk.Context, portID string) error {
	cap := k.portKeeper.BindPort(ctx, portID)
	return k.ClaimCapability(ctx, cap, host.PortPath(portID))
}

// GetPort returns the portID for the transfer module. Used in ExportGenesis
func (k Keeper) GetPort(ctx sdk.Context) string {
	store := ctx.KVStore(k.storeKey)
	return string(store.Get(types.PortKey()))
}

// SetPort sets the portID for the CCV module. Used in InitGenesis
func (k Keeper) SetPort(ctx sdk.Context, portID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.PortKey(), []byte(portID))
}

// AuthenticateCapability wraps the scopedKeeper's AuthenticateCapability function
func (k Keeper) AuthenticateCapability(ctx sdk.Context, cap *capabilitytypes.Capability, name string) bool {
	return k.scopedKeeper.AuthenticateCapability(ctx, cap, name)
}

// ClaimCapability claims a capability that the IBC module passes to it
func (k Keeper) ClaimCapability(ctx sdk.Context, cap *capabilitytypes.Capability, name string) error {
	return k.scopedKeeper.ClaimCapability(ctx, cap, name)
}

// SetProviderClientID sets the clientID for the client to the provider.
// Set in InitGenesis
func (k Keeper) SetProviderClientID(ctx sdk.Context, clientID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ProviderClientIDKey(), []byte(clientID))
}

// GetProviderClientID gets the clientID for the client to the provider.
func (k Keeper) GetProviderClientID(ctx sdk.Context) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	clientIdBytes := store.Get(types.ProviderClientIDKey())
	if clientIdBytes == nil {
		return "", false
	}
	return string(clientIdBytes), true
}

// SetProviderChannel sets the channelID for the channel to the provider.
func (k Keeper) SetProviderChannel(ctx sdk.Context, channelID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ProviderChannelKey(), []byte(channelID))
}

// GetProviderChannel gets the channelID for the channel to the provider.
func (k Keeper) GetProviderChannel(ctx sdk.Context) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	channelIdBytes := store.Get(types.ProviderChannelKey())
	if len(channelIdBytes) == 0 {
		return "", false
	}
	return string(channelIdBytes), true
}

// DeleteProviderChannel deletes the channelID for the channel to the provider.
func (k Keeper) DeleteProviderChannel(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ProviderChannelKey())
}

// SetPendingChanges sets the pending validator set change packet that haven't been flushed to ABCI
func (k Keeper) SetPendingChanges(ctx sdk.Context, updates ccv.ValidatorSetChangePacketData) {
	store := ctx.KVStore(k.storeKey)
	bz, err := updates.Marshal()
	if err != nil {
		// This should never happen
		panic(fmt.Errorf("failed to marshal PendingChanges: %w", err))
	}
	store.Set(types.PendingChangesKey(), bz)
}

// GetPendingChanges gets the pending changes that haven't been flushed over ABCI
func (k Keeper) GetPendingChanges(ctx sdk.Context) (*ccv.ValidatorSetChangePacketData, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingChangesKey())
	if bz == nil {
		return nil, false
	}
	var data ccv.ValidatorSetChangePacketData
	if err := data.Unmarshal(bz); err != nil {
		// This should never happen as PendingChanges is expected
		// to be correctly serialized in SetPendingChanges
		panic(fmt.Errorf("failed to unmarshal PendingChanges: %w", err))
	}
	return &data, true
}

// DeletePendingChanges deletes the pending changes after they've been flushed to ABCI
func (k Keeper) DeletePendingChanges(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PendingChangesKey())
}

func (k Keeper) GetInitGenesisHeight(ctx sdk.Context) int64 {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.InitGenesisHeightKey())
	if bz == nil {
		panic("last standalone height not set")
	}
	height := sdk.BigEndianToUint64(bz)
	return int64(height)
}

func (k Keeper) SetInitGenesisHeight(ctx sdk.Context, height int64) {
	bz := sdk.Uint64ToBigEndian(uint64(height))
	store := ctx.KVStore(k.storeKey)
	store.Set(types.InitGenesisHeightKey(), bz)
}

func (k Keeper) IsPreCCV(ctx sdk.Context) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PreCCVKey())
	return bz != nil
}

func (k Keeper) SetPreCCVTrue(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	bz := sdk.Uint64ToBigEndian(uint64(1))
	store.Set(types.PreCCVKey(), bz)
}

func (k Keeper) DeletePreCCV(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PreCCVKey())
}

func (k Keeper) SetInitialValSet(ctx sdk.Context, initialValSet []tmtypes.ValidatorUpdate) {
	store := ctx.KVStore(k.storeKey)
	initialValSetState := ccv.ConsumerGenesisState{
		InitialValSet: initialValSet,
	}
	bz := k.cdc.MustMarshal(&initialValSetState)
	store.Set(types.InitialValSetKey(), bz)
}

func (k Keeper) GetInitialValSet(ctx sdk.Context) []tmtypes.ValidatorUpdate {
	store := ctx.KVStore(k.storeKey)
	initialValSet := ccv.ConsumerGenesisState{}
	bz := store.Get(types.InitialValSetKey())
	if bz != nil {
		k.cdc.MustUnmarshal(bz, &initialValSet)
		return initialValSet.InitialValSet
	}
	return []tmtypes.ValidatorUpdate{}
}

func (k Keeper) GetLastStandaloneValidators(ctx sdk.Context) []stakingtypes.Validator {
	if !k.IsPreCCV(ctx) || k.standaloneStakingKeeper == nil {
		panic("cannot get last standalone validators if not in pre-ccv state, or if standalone staking keeper is nil")
	}
	return k.standaloneStakingKeeper.GetLastValidators(ctx)
}

// GetElapsedPacketMaturityTimes returns a slice of already elapsed PacketMaturityTimes, sorted by maturity times,
// i.e., the slice contains the IDs of the matured VSCPackets.
func (k Keeper) GetElapsedPacketMaturityTimes(ctx sdk.Context) (maturingVSCPackets []ccv.MaturingVSCPacket) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PacketMaturityTimeBytePrefix})

	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var maturingVSCPacket ccv.MaturingVSCPacket
		if err := maturingVSCPacket.Unmarshal(iterator.Value()); err != nil {
			// An error here would indicate something is very wrong,
			// the MaturingVSCPackets are assumed to be correctly serialized in SetPacketMaturityTime.
			panic(fmt.Errorf("failed to unmarshal MaturingVSCPacket: %w", err))
		}

		// If the current block time is before maturity time then stop the iteration.
		// This is possible since the iteration over PacketMaturityTimes is in order
		// of maturity times
		if ctx.BlockTime().Before(maturingVSCPacket.MaturityTime) {
			break
		}

		maturingVSCPackets = append(maturingVSCPackets, maturingVSCPacket)
	}
	return maturingVSCPackets
}

// GetAllPacketMaturityTimes returns a slice of all PacketMaturityTimes, sorted by maturity times.
//
// Note that PacketMaturityTimes are stored under keys with the following format:
// PacketMaturityTimeBytePrefix | maturityTime.UnixNano() | vscID
// Thus, the returned array is in ascending order of maturityTimes.
// If two entries have the same maturityTime, then they are ordered by vscID.
func (k Keeper) GetAllPacketMaturityTimes(ctx sdk.Context) (maturingVSCPackets []ccv.MaturingVSCPacket) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PacketMaturityTimeBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		var maturingVSCPacket ccv.MaturingVSCPacket
		if err := maturingVSCPacket.Unmarshal(iterator.Value()); err != nil {
			// An error here would indicate something is very wrong,
			// the MaturingVSCPackets are assumed to be correctly serialized in SetPacketMaturityTime.
			panic(fmt.Errorf("failed to unmarshal MaturingVSCPacket: %w", err))
		}

		maturingVSCPackets = append(maturingVSCPackets, maturingVSCPacket)
	}
	return maturingVSCPackets
}

// SetPacketMaturityTime sets the maturity time for a given received VSC packet id
func (k Keeper) SetPacketMaturityTime(ctx sdk.Context, vscId uint64, maturityTime time.Time) {
	store := ctx.KVStore(k.storeKey)
	maturingVSCPacket := ccv.MaturingVSCPacket{
		VscId:        vscId,
		MaturityTime: maturityTime,
	}
	bz, err := maturingVSCPacket.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// maturingVSCPacket is instantiated in this method and should be able to be marshaled.
		panic(fmt.Errorf("failed to marshal MaturingVSCPacket: %w", err))
	}
	store.Set(types.PacketMaturityTimeKey(vscId, maturityTime), bz)
}

// PacketMaturityExists checks whether the packet maturity time for a given vscId and maturityTime exists.
//
// Note: this method is only used in testing.
func (k Keeper) PacketMaturityTimeExists(ctx sdk.Context, vscId uint64, maturityTime time.Time) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PacketMaturityTimeKey(vscId, maturityTime))
	return bz != nil
}

// DeletePacketMaturityTimes deletes the packet maturity time for a given vscId and maturityTime
func (k Keeper) DeletePacketMaturityTimes(ctx sdk.Context, vscId uint64, maturityTime time.Time) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PacketMaturityTimeKey(vscId, maturityTime))
}

// VerifyProviderChain verifies that the chain trying to connect on the channel handshake
// is the expected provider chain.
func (k Keeper) VerifyProviderChain(ctx sdk.Context, connectionHops []string) error {
	if len(connectionHops) != 1 {
		return sdkerrors.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to provider chain")
	}
	connectionID := connectionHops[0]
	conn, ok := k.connectionKeeper.GetConnection(ctx, connectionID)
	if !ok {
		return sdkerrors.Wrapf(conntypes.ErrConnectionNotFound, "connection not found for connection ID: %s", connectionID)
	}
	// Verify that client id is expected clientID
	expectedClientId, ok := k.GetProviderClientID(ctx)
	if !ok {
		return sdkerrors.Wrapf(clienttypes.ErrInvalidClient, "could not find provider client id")
	}
	if expectedClientId != conn.ClientId {
		return sdkerrors.Wrapf(clienttypes.ErrInvalidClient, "invalid client: %s, channel must be built on top of client: %s", conn.ClientId, expectedClientId)
	}

	return nil
}

// SetHeightValsetUpdateID sets the valset update id for a given block height
func (k Keeper) SetHeightValsetUpdateID(ctx sdk.Context, height, valsetUpdateId uint64) {
	store := ctx.KVStore(k.storeKey)
	valBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(valBytes, valsetUpdateId)
	store.Set(types.HeightValsetUpdateIDKey(height), valBytes)
}

// GetHeightValsetUpdateID gets the valset update id recorded for a given block height
func (k Keeper) GetHeightValsetUpdateID(ctx sdk.Context, height uint64) uint64 {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.HeightValsetUpdateIDKey(height))
	if bz == nil {
		return 0
	}
	return binary.BigEndian.Uint64(bz)
}

// DeleteHeightValsetUpdateID deletes the valset update id for a given block height
func (k Keeper) DeleteHeightValsetUpdateID(ctx sdk.Context, height uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.HeightValsetUpdateIDKey(height))
}

// GetAllHeightToValsetUpdateIDs returns a list of all the block heights to valset update IDs in the store
//
// Note that the block height to vscID mapping is stored under keys with the following format:
// HeightValsetUpdateIDBytePrefix | height
// Thus, the returned array is in ascending order of heights.
func (k Keeper) GetAllHeightToValsetUpdateIDs(ctx sdk.Context) (heightToValsetUpdateIDs []ccv.HeightToValsetUpdateID) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.HeightValsetUpdateIDBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		height := binary.BigEndian.Uint64(iterator.Key()[1:])
		vscID := binary.BigEndian.Uint64(iterator.Value())

		heightToValsetUpdateIDs = append(heightToValsetUpdateIDs, ccv.HeightToValsetUpdateID{
			Height:         height,
			ValsetUpdateId: vscID,
		})
	}

	return heightToValsetUpdateIDs
}

// OutstandingDowntime returns the outstanding downtime flag for a given validator
func (k Keeper) OutstandingDowntime(ctx sdk.Context, address sdk.ConsAddress) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.OutstandingDowntimeKey(address))
	return bz != nil
}

// SetOutstandingDowntime sets the outstanding downtime flag for a given validator
func (k Keeper) SetOutstandingDowntime(ctx sdk.Context, address sdk.ConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.OutstandingDowntimeKey(address), []byte{})
}

// DeleteOutstandingDowntime deletes the outstanding downtime flag for the given validator consensus address
func (k Keeper) DeleteOutstandingDowntime(ctx sdk.Context, consAddress string) {
	consAddr, err := sdk.ConsAddressFromBech32(consAddress)
	if err != nil {
		return // TODO: this should panic with appropriate tests to validate the panic wont happen in normal cases.
	}
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.OutstandingDowntimeKey(consAddr))
}

// GetAllOutstandingDowntimes gets an array of the validator addresses of outstanding downtime flags
//
// Note that the outstanding downtime flags are stored under keys with the following format:
// OutstandingDowntimeBytePrefix | consAddress
// Thus, the returned array is in ascending order of consAddresses.
func (k Keeper) GetAllOutstandingDowntimes(ctx sdk.Context) (downtimes []ccv.OutstandingDowntime) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.OutstandingDowntimeBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		addrBytes := iterator.Key()[1:]
		addr := sdk.ConsAddress(addrBytes).String()

		downtimes = append(downtimes, ccv.OutstandingDowntime{
			ValidatorConsensusAddress: addr,
		})
	}

	return downtimes
}

// SetCCValidator sets a cross-chain validator under its validator address
func (k Keeper) SetCCValidator(ctx sdk.Context, v ccv.CrossChainValidator) {
	store := ctx.KVStore(k.storeKey)
	bz := k.cdc.MustMarshal(&v)

	store.Set(types.CrossChainValidatorKey(v.Address), bz)
}

// GetCCValidator returns a cross-chain validator for a given address
func (k Keeper) GetCCValidator(ctx sdk.Context, addr []byte) (validator ccv.CrossChainValidator, found bool) {
	store := ctx.KVStore(k.storeKey)
	v := store.Get(types.CrossChainValidatorKey(addr))
	if v == nil {
		return
	}
	k.cdc.MustUnmarshal(v, &validator)
	found = true

	return
}

// DeleteCCValidator deletes a cross-chain validator for a given address
func (k Keeper) DeleteCCValidator(ctx sdk.Context, addr []byte) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.CrossChainValidatorKey(addr))
}

// GetAllCCValidator returns all cross-chain validators
//
// Note that the cross-chain validators are stored under keys with the following format:
// CrossChainValidatorBytePrefix | address
// Thus, the returned array is in ascending order of addresses.
func (k Keeper) GetAllCCValidator(ctx sdk.Context) (validators []ccv.CrossChainValidator) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.CrossChainValidatorBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		val := ccv.CrossChainValidator{}
		k.cdc.MustUnmarshal(iterator.Value(), &val)
		validators = append(validators, val)
	}

	return validators
}

// SetPendingPackets sets the pending CCV packets
func (k Keeper) SetPendingPackets(ctx sdk.Context, packets ccv.ConsumerPacketDataList) {
	store := ctx.KVStore(k.storeKey)
	bz, err := packets.Marshal()
	if err != nil {
		// This should never happen
		panic(fmt.Errorf("failed to marshal ConsumerPacketDataList: %w", err))
	}
	store.Set(types.PendingDataPacketsKey(), bz)
}

// GetPendingPackets returns the pending CCV packets from the store
func (k Keeper) GetPendingPackets(ctx sdk.Context) ccv.ConsumerPacketDataList {
	var packets ccv.ConsumerPacketDataList

	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingDataPacketsKey())
	if bz == nil {
		return packets
	}

	err := packets.Unmarshal(bz)
	if err != nil {
		// An error here would indicate something is very wrong,
		// the PendingPackets are assumed to be correctly serialized in SetPendingPackets.
		panic(fmt.Errorf("failed to unmarshal pending data packets: %w", err))
	}

	return packets
}

// DeletePendingDataPackets clears the pending data packets in store
func (k Keeper) DeletePendingDataPackets(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PendingDataPacketsKey())
}

// AppendPendingDataPacket appends the given data packet to the pending data packets in store
func (k Keeper) AppendPendingPacket(ctx sdk.Context, packet ...ccv.ConsumerPacketData) {
	pending := k.GetPendingPackets(ctx)
	list := append(pending.GetList(), packet...)
	k.SetPendingPackets(ctx, ccv.ConsumerPacketDataList{List: list})
}

func (k Keeper) MarkAsPrevStandaloneChain(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.PrevStandaloneChainKey(), []byte{})
}

func (k Keeper) IsPrevStandaloneChain(ctx sdk.Context) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Has(types.PrevStandaloneChainKey())
}

// SetStandaloneTransferChannelID sets the channelID of an existing transfer channel,
// for a chain which used to be a standalone chain.
func (k Keeper) SetStandaloneTransferChannelID(ctx sdk.Context, channelID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.StandaloneTransferChannelIDKey(), []byte(channelID))
}

// GetStandaloneTransferChannelID returns the channelID of an existing transfer channel,
// for a chain which used to be a standalone chain.
func (k Keeper) GetStandaloneTransferChannelID(ctx sdk.Context) string {
	store := ctx.KVStore(k.storeKey)
	return string(store.Get(types.StandaloneTransferChannelIDKey()))
}
