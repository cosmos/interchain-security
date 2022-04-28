package keeper

import (
	"bytes"
	"encoding/binary"
	"encoding/json"

	"github.com/cosmos/cosmos-sdk/codec"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	capabilitykeeper "github.com/cosmos/cosmos-sdk/x/capability/keeper"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/tendermint/tendermint/libs/log"
)

// Keeper defines the Cross-Chain Validation Consumer Keeper
type Keeper struct {
	storeKey          sdk.StoreKey
	cdc               codec.BinaryCodec
	paramSpace        paramtypes.Subspace
	scopedKeeper      capabilitykeeper.ScopedKeeper
	channelKeeper     ccv.ChannelKeeper
	portKeeper        ccv.PortKeeper
	connectionKeeper  ccv.ConnectionKeeper
	clientKeeper      ccv.ClientKeeper
	slashingKeeper    ccv.SlashingKeeper
	hooks             ccv.ConsumerHooks
	bankKeeper        ccv.BankKeeper
	accountKeeper     ccv.AccountKeeper
	ibcTransferKeeper ccv.IBCTransferKeeper
	ibcCoreKeeper     ccv.IBCCoreKeeper
	feeCollectorName  string
}

// NewKeeper creates a new Consumer Keeper instance
// NOTE: the feeCollectorName is in reference to the consumer-chain fee
// collector (and not the provider chain)
func NewKeeper(
	cdc codec.BinaryCodec, key sdk.StoreKey, paramSpace paramtypes.Subspace,
	scopedKeeper capabilitykeeper.ScopedKeeper,
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
		paramSpace:        paramSpace,
		scopedKeeper:      scopedKeeper,
		channelKeeper:     channelKeeper,
		portKeeper:        portKeeper,
		connectionKeeper:  connectionKeeper,
		clientKeeper:      clientKeeper,
		slashingKeeper:    slashingKeeper,
		bankKeeper:        bankKeeper,
		accountKeeper:     accountKeeper,
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
// in order to expose it to the ICS20 transfer handler.
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
	return string(store.Get(types.PortKey))
}

// SetPort sets the portID for the transfer module. Used in InitGenesis
func (k Keeper) SetPort(ctx sdk.Context, portID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.PortKey, []byte(portID))
}

// AuthenticateCapability wraps the scopedKeeper's AuthenticateCapability function
func (k Keeper) AuthenticateCapability(ctx sdk.Context, cap *capabilitytypes.Capability, name string) bool {
	return k.scopedKeeper.AuthenticateCapability(ctx, cap, name)
}

// ClaimCapability allows the transfer module that can claim a capability that IBC module
// passes to it
func (k Keeper) ClaimCapability(ctx sdk.Context, cap *capabilitytypes.Capability, name string) error {
	return k.scopedKeeper.ClaimCapability(ctx, cap, name)
}

// SetChannelStatus sets the status of a CCV channel with the given status
func (k Keeper) SetChannelStatus(ctx sdk.Context, channelID string, status ccv.Status) {
	store := ctx.KVStore(k.storeKey)
	store.Set(ccv.ChannelStatusKey(channelID), []byte{byte(status)})
}

// GetChannelStatus gets the status of a CCV channel
func (k Keeper) GetChannelStatus(ctx sdk.Context, channelID string) ccv.Status {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(ccv.ChannelStatusKey(channelID))
	if bz == nil {
		return ccv.UNINITIALIZED
	}
	return ccv.Status(bz[0])
}

// SetProviderClient sets the provider clientID that is validating the chain.
// Set in InitGenesis
func (k Keeper) SetProviderClient(ctx sdk.Context, clientID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ProviderClientKey(), []byte(clientID))
}

// GetProviderClient gets the provider clientID that is validating the chain.
func (k Keeper) GetProviderClient(ctx sdk.Context) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	clientIdBytes := store.Get(types.ProviderClientKey())
	if clientIdBytes == nil {
		return "", false
	}
	return string(clientIdBytes), true
}

// SetProviderChannel sets the provider channelID that is validating the chain.
func (k Keeper) SetProviderChannel(ctx sdk.Context, channelID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ProviderChannelKey(), []byte(channelID))
}

// GetProviderChannel gets the provider channelID that is validating the chain.
func (k Keeper) GetProviderChannel(ctx sdk.Context) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	channelIdBytes := store.Get(types.ProviderChannelKey())
	if len(channelIdBytes) == 0 {
		return "", false
	}
	return string(channelIdBytes), true
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
	data.Unmarshal(bz)
	return &data, true
}

// DeletePendingChanges deletes the pending changes after they've been flushed to ABCI
func (k Keeper) DeletePendingChanges(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PendingChangesKey())
}

// IterateUnbondingTime iterates through the unbonding times set in the store
func (k Keeper) IterateUnbondingTime(ctx sdk.Context, cb func(seq, timeNs uint64) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte(types.UnbondingTimePrefix))

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		seqBytes := iterator.Key()[len([]byte(types.UnbondingTimePrefix)):]
		seq := binary.BigEndian.Uint64(seqBytes)

		timeNs := binary.BigEndian.Uint64(iterator.Value())

		if cb(seq, timeNs) {
			break
		}
	}
}

// SetUnbondingTime sets the unbonding time for a given received packet sequence
func (k Keeper) SetUnbondingTime(ctx sdk.Context, sequence, unbondingTime uint64) {
	store := ctx.KVStore(k.storeKey)
	timeBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(timeBytes, unbondingTime)
	store.Set(types.UnbondingTimeKey(sequence), timeBytes)
}

// GetUnbondingTime gets the unbonding time for a given received packet sequence
func (k Keeper) GetUnbondingTime(ctx sdk.Context, sequence uint64) uint64 {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.UnbondingTimeKey(sequence))
	if bz == nil {
		return 0
	}
	return binary.BigEndian.Uint64(bz)
}

// DeleteUnbondingTime deletes the unbonding time
func (k Keeper) DeleteUnbondingTime(ctx sdk.Context, sequence uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.UnbondingTimeKey(sequence))
}

// IterateUnbondingPacket iterates through the unbonding packets set in the store
func (k Keeper) IterateUnbondingPacket(ctx sdk.Context, cb func(seq uint64, packet channeltypes.Packet) bool) error {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte(types.UnbondingPacketPrefix))

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		seqBytes := iterator.Key()[len([]byte(types.UnbondingPacketPrefix)):]
		seq := binary.BigEndian.Uint64(seqBytes)

		var packet channeltypes.Packet
		err := packet.Unmarshal(iterator.Value())
		if err != nil {
			return err
		}

		if cb(seq, packet) {
			break
		}
	}
	return nil
}

// SetUnbondingPacket sets the unbonding packet for a given received packet sequence
func (k Keeper) SetUnbondingPacket(ctx sdk.Context, sequence uint64, packet channeltypes.Packet) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := packet.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.UnbondingPacketKey(sequence), bz)
	return nil
}

// GetUnbondingPacket gets the unbonding packet for a given received packet sequence
func (k Keeper) GetUnbondingPacket(ctx sdk.Context, sequence uint64) (*channeltypes.Packet, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.UnbondingPacketKey(sequence))
	if bz == nil {
		return nil, sdkerrors.Wrapf(channeltypes.ErrInvalidPacket, "packet does not exist at sequence: %d", sequence)
	}
	var packet channeltypes.Packet
	err := packet.Unmarshal(bz)
	if err != nil {
		return nil, err
	}
	return &packet, nil
}

// DeleteUnbondingPacket deletes the unbonding packet
func (k Keeper) DeleteUnbondingPacket(ctx sdk.Context, sequence uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.UnbondingPacketKey(sequence))
}

// VerifyProviderChain verifies that the chain trying to connect on the channel handshake
// is the expected provider chain.
func (k Keeper) VerifyProviderChain(ctx sdk.Context, channelID string, connectionHops []string) error {
	// Verify CCV channel is in Initialized state
	status := k.GetChannelStatus(ctx, channelID)
	if status != ccv.INITIALIZING {
		return sdkerrors.Wrap(ccv.ErrInvalidStatus, "CCV channel status must be in Initializing state")
	}
	if len(connectionHops) != 1 {
		return sdkerrors.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to provider chain")
	}
	connectionID := connectionHops[0]
	conn, ok := k.connectionKeeper.GetConnection(ctx, connectionID)
	if !ok {
		return sdkerrors.Wrapf(conntypes.ErrConnectionNotFound, "connection not found for connection ID: %s", connectionID)
	}
	// Verify that client id is expected clientID
	expectedClientId, ok := k.GetProviderClient(ctx)
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

// ClearOutstandingDowntime clears the outstanding downtime flag for a given validator
func (k Keeper) ClearOutstandingDowntime(ctx sdk.Context, address string) {
	consAddr, err := sdk.ConsAddressFromBech32(address)
	if err != nil {
		return
	}
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.OutstandingDowntimeKey(consAddr))
}

// SetCCValidator sets a cross-chain validator under its validator address
func (k Keeper) SetCCValidator(ctx sdk.Context, v types.CrossChainValidator) {
	store := ctx.KVStore(k.storeKey)
	bz := k.cdc.MustMarshal(&v)

	store.Set(types.GetCrossChainValidatorKey(v.Address), bz)
}

// GetCCValidator returns a cross-chain validator for a given address
func (k Keeper) GetCCValidator(ctx sdk.Context, addr []byte) (validator types.CrossChainValidator, found bool) {
	store := ctx.KVStore(k.storeKey)
	v := store.Get(types.GetCrossChainValidatorKey(addr))
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
	store.Delete(types.GetCrossChainValidatorKey(addr))
}

// GetAllCCValidator returns all cross-chain validators
func (k Keeper) GetAllCCValidator(ctx sdk.Context) (validators []types.CrossChainValidator) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte(types.CrossChainValidatorPrefix))

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		val := types.CrossChainValidator{}
		k.cdc.MustUnmarshal(iterator.Value(), &val)
		validators = append(validators, val)
	}

	return validators
}

// SetPendingSlashRequests sets the pending slash requests in store
func (k Keeper) SetPendingSlashRequests(ctx sdk.Context, requests []types.SlashRequest) {
	store := ctx.KVStore(k.storeKey)
	buf := &bytes.Buffer{}
	err := json.NewEncoder(buf).Encode(&requests)
	if err != nil {
		panic("failed to encode json")
	}
	store.Set([]byte(types.PendingSlashRequestsPrefix), buf.Bytes())
}

// GetPendingSlashRequest returns the pending slash requests in store
func (k Keeper) GetPendingSlashRequests(ctx sdk.Context) (requests []types.SlashRequest) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get([]byte(types.PendingSlashRequestsPrefix))
	if bz == nil {
		return
	}
	buf := bytes.NewBuffer(bz)
	json.NewDecoder(buf).Decode(&requests)
	if len(requests) == 0 {
		panic("failed to decode json")
	}

	return
}

// AppendPendingSlashRequests appends the given slash request to the pending slash requests in store
func (k Keeper) AppendPendingSlashRequests(ctx sdk.Context, req types.SlashRequest) {
	requests := k.GetPendingSlashRequests(ctx)
	requests = append(requests, req)
	k.SetPendingSlashRequests(ctx, requests)
}

// ClearPendingSlashRequests clears the pending slash requests in store
func (k Keeper) ClearPendingSlashRequests(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete([]byte(types.PendingSlashRequestsPrefix))
}
