package keeper

import (
	"encoding/binary"
	"fmt"

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

// IteratePacketMaturityTime iterates through the VSC packet maturity times set in the store
func (k Keeper) IteratePacketMaturityTime(ctx sdk.Context, cb func(vscId, timeNs uint64) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PacketMaturityTimeBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		// Extract bytes following the 1 byte prefix
		seqBytes := iterator.Key()[1:]
		seq := binary.BigEndian.Uint64(seqBytes)

		timeNs := binary.BigEndian.Uint64(iterator.Value())

		if cb(seq, timeNs) {
			break
		}
	}
}

// SetPacketMaturityTime sets the maturity time for a given received VSC packet id
func (k Keeper) SetPacketMaturityTime(ctx sdk.Context, vscId, maturityTime uint64) {
	store := ctx.KVStore(k.storeKey)
	timeBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(timeBytes, maturityTime)
	store.Set(types.PacketMaturityTimeKey(vscId), timeBytes)
}

// GetPacketMaturityTime gets the maturity time for a given received VSC packet id
func (k Keeper) GetPacketMaturityTime(ctx sdk.Context, vscId uint64) uint64 {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PacketMaturityTimeKey(vscId))
	if bz == nil {
		return 0
	}
	return binary.BigEndian.Uint64(bz)
}

// DeletePacketMaturityTime deletes the packet maturity time for a given received VSC packet id
func (k Keeper) DeletePacketMaturityTime(ctx sdk.Context, vscId uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PacketMaturityTimeKey(vscId))
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

// IterateHeightToValsetUpdateID iterates over the block height to valset update ID mapping in store
func (k Keeper) IterateHeightToValsetUpdateID(ctx sdk.Context, cb func(height, vscID uint64) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.HeightValsetUpdateIDBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		heightBytes := iterator.Key()[1:]
		height := binary.BigEndian.Uint64(heightBytes)

		vscID := binary.BigEndian.Uint64(iterator.Value())

		if !cb(height, vscID) {
			break
		}
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

// IterateOutstandingDowntime iterates over the validator addresses of outstanding downtime flags
func (k Keeper) IterateOutstandingDowntime(ctx sdk.Context, cb func(address string) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.OutstandingDowntimeBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		addrBytes := iterator.Key()[1:]
		addr := sdk.ConsAddress(addrBytes).String()
		if !cb(addr) {
			break
		}
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

// GetAllCCValidator returns all cross-chain validators
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

// SetPendingSlashRequests sets the pending slash requests in store
func (k Keeper) SetPendingSlashRequests(ctx sdk.Context, requests types.SlashRequests) {
	store := ctx.KVStore(k.storeKey)
	bz, err := requests.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to encode slash request json: %w", err))
	}
	store.Set([]byte{types.PendingSlashRequestsBytePrefix}, bz)
}

// GetPendingSlashRequest returns the pending slash requests in store
func (k Keeper) GetPendingSlashRequests(ctx sdk.Context) types.SlashRequests {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get([]byte{types.PendingSlashRequestsBytePrefix})
	if bz == nil {
		return types.SlashRequests{}
	}

	var sr types.SlashRequests
	err := sr.Unmarshal(bz)
	if err != nil {
		panic(fmt.Errorf("failed to decode slash request json: %w", err))
	}

	return sr
}

// ClearPendingSlashRequests clears the pending slash requests in store
func (k Keeper) DeletePendingSlashRequests(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete([]byte{types.PendingSlashRequestsBytePrefix})
}

// AppendPendingSlashRequests appends the given slash request to the pending slash requests in store
func (k Keeper) AppendPendingSlashRequests(ctx sdk.Context, req types.SlashRequest) {
	sr := k.GetPendingSlashRequests(ctx)
	srArray := sr.GetRequests()
	srArray = append(srArray, req)
	k.SetPendingSlashRequests(ctx, types.SlashRequests{Requests: srArray})
}
