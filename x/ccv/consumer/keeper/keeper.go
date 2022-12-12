package keeper

import (
	"fmt"
	"time"

	"github.com/cosmos/cosmos-sdk/codec"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/tendermint/tendermint/libs/log"
)

// Keeper defines the Cross-Chain Validation Consumer Keeper
type Keeper struct {
	storeKey          sdk.StoreKey
	cdc               codec.BinaryCodec
	paramStore        paramtypes.Subspace
	scopedKeeper      ccv.ScopedKeeper
	channelKeeper     ccv.ChannelKeeper
	portKeeper        ccv.PortKeeper
	connectionKeeper  ccv.ConnectionKeeper
	clientKeeper      ccv.ClientKeeper
	slashingKeeper    ccv.SlashingKeeper
	hooks             ccv.ConsumerHooks
	bankKeeper        ccv.BankKeeper
	authKeeper        ccv.AccountKeeper
	ibcTransferKeeper ccv.IBCTransferKeeper
	ibcCoreKeeper     ccv.IBCCoreKeeper
	feeCollectorName  string
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
		paramSpace = paramSpace.WithKeyTable(types.ParamKeyTable())
	}

	return Keeper{
		storeKey:          key,
		cdc:               cdc,
		paramStore:        paramSpace,
		scopedKeeper:      scopedKeeper,
		channelKeeper:     channelKeeper,
		portKeeper:        portKeeper,
		connectionKeeper:  connectionKeeper,
		clientKeeper:      clientKeeper,
		slashingKeeper:    slashingKeeper,
		bankKeeper:        bankKeeper,
		authKeeper:        accountKeeper,
		ibcTransferKeeper: ibcTransferKeeper,
		ibcCoreKeeper:     ibcCoreKeeper,
		feeCollectorName:  feeCollectorName,
	}
}

// Logger returns a module-specific logger.
func (k Keeper) Logger(ctx sdk.Context) log.Logger {
	return ctx.Logger().With("module", "x/"+host.ModuleName+"-"+types.ModuleName)
}

func (k *Keeper) SetHooks(sh ccv.ConsumerHooks) *Keeper {
	if k.hooks != nil {
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
func (k Keeper) SetPendingChanges(ctx sdk.Context, updates ccv.ValidatorSetChangePacketData) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := updates.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.PendingChangesKey(), bz)
	return nil
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
		panic(fmt.Errorf("pending changes could not be unmarshaled: %w", err))
	}
	return &data, true
}

// DeletePendingChanges deletes the pending changes after they've been flushed to ABCI
func (k Keeper) DeletePendingChanges(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PendingChangesKey())
}

// GetVSCPacketQueueTimeSlice gets a specific VSC packet queue timeslice.
// A timeslice is a slice of IDs corresponding to received VSC packets
// that reach maturity at a certain time.
func (k Keeper) GetVSCPacketQueueTimeSlice(ctx sdk.Context, timestamp time.Time) (vscIDs []uint64) {
	store := ctx.KVStore(k.storeKey)

	bz := store.Get(types.VSCPacketQueueKey(timestamp))
	if bz == nil {
		return []uint64{}
	}

	validatorSetChangeIDs := types.ValidatorSetChangeIDs{}
	k.cdc.MustUnmarshal(bz, &validatorSetChangeIDs)

	return validatorSetChangeIDs.Ids
}

// InsertVSCPacketQueue inserts the ID of a VSC packet to the appropriate timeslice
// in the VSCPacketQueue.
func (k Keeper) InsertVSCPacketQueue(ctx sdk.Context, vscID uint64, maturityTime time.Time) {
	vscIDs := k.GetVSCPacketQueueTimeSlice(ctx, maturityTime)
	vscIDs = append(vscIDs, vscID)
	store := ctx.KVStore(k.storeKey)
	bz := k.cdc.MustMarshal(&types.ValidatorSetChangeIDs{Ids: vscIDs})
	store.Set(types.VSCPacketQueueKey(maturityTime), bz)
}

// VSCPacketQueueIterator returns all the VSC packet queue timeslices from time 0 until endTime.
func (k Keeper) VSCPacketQueueIterator(ctx sdk.Context, endTime time.Time) sdk.Iterator {
	store := ctx.KVStore(k.storeKey)
	return store.Iterator([]byte{types.VSCPacketQueueBytePrefix},
		sdk.InclusiveEndBytes(types.VSCPacketQueueKey(endTime)))
}

// DequeueAllMatureVSCPacketQueue returns a concatenated list of all IDs of matured VSC packets
// and deletes the timeslices from the VSC packet queue.
func (k Keeper) DequeueAllMatureVSCPacketQueue(ctx sdk.Context) (vscIDs []uint64) {
	store := ctx.KVStore(k.storeKey)

	// gets an iterator for all timeslices from time 0 until the current Blockheader time
	iterator := k.VSCPacketQueueIterator(ctx, ctx.BlockHeader().Time)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		timeslice := types.ValidatorSetChangeIDs{}
		value := iterator.Value()
		k.cdc.MustUnmarshal(value, &timeslice)

		vscIDs = append(vscIDs, timeslice.Ids...)

		store.Delete(iterator.Key())
	}

	return vscIDs
}

// GetAllVSCPacketMaturityTimes returns the maturity times of all received VSC packets.
//
// Note: The order of iteration is irrelevant as it returns all maturity times.
func (k Keeper) GetAllVSCPacketMaturityTimes(ctx sdk.Context) []consumertypes.MaturingVSCPacket {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.VSCPacketQueueBytePrefix})
	defer iterator.Close()

	maturingVSCPacket := []consumertypes.MaturingVSCPacket{}
	for ; iterator.Valid(); iterator.Next() {
		maturityTime, err := sdk.ParseTimeBytes(iterator.Key()[1:])
		if err != nil {
			panic(fmt.Errorf("failed to parse key: %w", err))
		}
		timeslice := types.ValidatorSetChangeIDs{}
		value := iterator.Value()
		k.cdc.MustUnmarshal(value, &timeslice)

		for _, vscID := range timeslice.Ids {
			maturingVSCPacket = append(maturingVSCPacket,
				consumertypes.MaturingVSCPacket{VscId: vscID, MaturityTime: maturityTime})
		}
	}
	return maturingVSCPacket
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

// SetHeightValsetUpdateID sets the vscID for a given block height
func (k Keeper) SetHeightValsetUpdateID(ctx sdk.Context, height, vscID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.HeightValsetUpdateIDKey(height), sdk.Uint64ToBigEndian(vscID))
}

// GetHeightValsetUpdateID gets the valset update id recorded for a given block height
func (k Keeper) GetHeightValsetUpdateID(ctx sdk.Context, height uint64) uint64 {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.HeightValsetUpdateIDKey(height))
	if bz == nil {
		return 0
	}
	return sdk.BigEndianToUint64(bz)
}

// DeleteHeightValsetUpdateID deletes the valset update id for a given block height
func (k Keeper) DeleteHeightValsetUpdateID(ctx sdk.Context, height uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.HeightValsetUpdateIDKey(height))
}

// IterateHeightToValsetUpdateID iterates over the block height to valset update ID mapping in store.
//
// Note that the block height to valset update ID mapping is stored under keys with the following format:
// HeightValsetUpdateIDBytePrefix | height
// Thus, the iteration is in ascending order of heights.
func (k Keeper) IterateHeightToValsetUpdateID(ctx sdk.Context, cb func(height, vscID uint64)) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.HeightValsetUpdateIDBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		height := sdk.BigEndianToUint64(iterator.Key()[1:])
		vscID := sdk.BigEndianToUint64(iterator.Value())

		cb(height, vscID)
		// never stop the iteration
	}
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
		return
	}
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.OutstandingDowntimeKey(consAddr))
}

// IterateOutstandingDowntime iterates over the outstanding downtime flags.
//
// Note that the outstanding downtime flags are stored under keys with the following format:
// OutstandingDowntimeBytePrefix | consAddress
// Thus, the iteration is in ascending order of consAddresses.
func (k Keeper) IterateOutstandingDowntime(ctx sdk.Context, cb func(address string)) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.OutstandingDowntimeBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		addrBytes := iterator.Key()[1:]
		addr := sdk.ConsAddress(addrBytes).String()
		cb(addr)
		// never stop the iteration
	}
}

// SetCCValidator sets a cross-chain validator under its validator address
func (k Keeper) SetCCValidator(ctx sdk.Context, v types.CrossChainValidator) {
	store := ctx.KVStore(k.storeKey)
	bz := k.cdc.MustMarshal(&v)

	store.Set(types.CrossChainValidatorKey(v.Address), bz)
}

// GetCCValidator returns a cross-chain validator for a given address
func (k Keeper) GetCCValidator(ctx sdk.Context, addr []byte) (validator types.CrossChainValidator, found bool) {
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

// GetAllCCValidator returns all cross-chain validators.
//
// Note that the cross-chain validators are stored under keys with the following format:
// CrossChainValidatorBytePrefix | address
// Thus, the iteration is in ascending order of addresses.
func (k Keeper) GetAllCCValidator(ctx sdk.Context) (validators []types.CrossChainValidator) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.CrossChainValidatorBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		val := types.CrossChainValidator{}
		k.cdc.MustUnmarshal(iterator.Value(), &val)
		validators = append(validators, val)
	}

	return validators
}

// SetPendingPackets sets the pending CCV packets
func (k Keeper) SetPendingPackets(ctx sdk.Context, packets types.ConsumerPackets) {
	store := ctx.KVStore(k.storeKey)
	bz, err := packets.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to encode packet: %w", err))
	}
	store.Set([]byte{types.PendingDataPacketsBytePrefix}, bz)
}

// GetPendingPackets returns the pending CCV packets from the store
func (k Keeper) GetPendingPackets(ctx sdk.Context) types.ConsumerPackets {
	var packets types.ConsumerPackets

	store := ctx.KVStore(k.storeKey)
	bz := store.Get([]byte{types.PendingDataPacketsBytePrefix})
	if bz == nil {
		return packets
	}

	err := packets.Unmarshal(bz)
	if err != nil {
		panic(fmt.Errorf("failed to unmarshal pending data packets: %w", err))
	}

	return packets
}

// DeletePendingDataPackets clears the pending data packets in store
func (k Keeper) DeletePendingDataPackets(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete([]byte{types.PendingDataPacketsBytePrefix})
}

// AppendPendingDataPacket appends the given data packet to the pending data packets in store
func (k Keeper) AppendPendingPacket(ctx sdk.Context, packet ...types.ConsumerPacket) {
	pending := k.GetPendingPackets(ctx)
	list := append(pending.GetList(), packet...)
	k.SetPendingPackets(ctx, types.ConsumerPackets{List: list})
}

// GetHeightToValsetUpdateIDs returns all height to valset update id mappings in store
func (k Keeper) GetHeightToValsetUpdateIDs(ctx sdk.Context) []types.HeightToValsetUpdateID {
	heightToVCIDs := []types.HeightToValsetUpdateID{}
	k.IterateHeightToValsetUpdateID(ctx, func(height, vscID uint64) {
		hv := types.HeightToValsetUpdateID{
			Height:         height,
			ValsetUpdateId: vscID,
		}
		heightToVCIDs = append(heightToVCIDs, hv)
	})

	return heightToVCIDs
}

// GetOutstandingDowntimes returns all outstanding downtimes in store
func (k Keeper) GetOutstandingDowntimes(ctx sdk.Context) []consumertypes.OutstandingDowntime {
	outstandingDowntimes := []types.OutstandingDowntime{}
	k.IterateOutstandingDowntime(ctx, func(addr string) {
		od := types.OutstandingDowntime{
			ValidatorConsensusAddress: addr,
		}
		outstandingDowntimes = append(outstandingDowntimes, od)
	})
	return outstandingDowntimes
}
