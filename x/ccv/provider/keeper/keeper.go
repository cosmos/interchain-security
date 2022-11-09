package keeper

import (
	"bytes"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"time"

	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ibcexported "github.com/cosmos/ibc-go/v3/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	"github.com/tendermint/tendermint/libs/log"
)

// Keeper defines the Cross-Chain Validation Provider Keeper
type Keeper struct {
	storeKey         sdk.StoreKey
	cdc              codec.BinaryCodec
	paramSpace       paramtypes.Subspace
	scopedKeeper     ccv.ScopedKeeper
	channelKeeper    ccv.ChannelKeeper
	portKeeper       ccv.PortKeeper
	connectionKeeper ccv.ConnectionKeeper
	accountKeeper    ccv.AccountKeeper
	clientKeeper     ccv.ClientKeeper
	stakingKeeper    ccv.StakingKeeper
	slashingKeeper   ccv.SlashingKeeper
	feeCollectorName string
}

// NewKeeper creates a new provider Keeper instance
func NewKeeper(
	cdc codec.BinaryCodec, key sdk.StoreKey, paramSpace paramtypes.Subspace, scopedKeeper ccv.ScopedKeeper,
	channelKeeper ccv.ChannelKeeper, portKeeper ccv.PortKeeper,
	connectionKeeper ccv.ConnectionKeeper, clientKeeper ccv.ClientKeeper,
	stakingKeeper ccv.StakingKeeper, slashingKeeper ccv.SlashingKeeper,
	accountKeeper ccv.AccountKeeper, feeCollectorName string,
) Keeper {
	// set KeyTable if it has not already been set
	if !paramSpace.HasKeyTable() {
		paramSpace = paramSpace.WithKeyTable(types.ParamKeyTable())
	}

	return Keeper{
		cdc:              cdc,
		storeKey:         key,
		paramSpace:       paramSpace,
		scopedKeeper:     scopedKeeper,
		channelKeeper:    channelKeeper,
		portKeeper:       portKeeper,
		connectionKeeper: connectionKeeper,
		accountKeeper:    accountKeeper,
		clientKeeper:     clientKeeper,
		stakingKeeper:    stakingKeeper,
		slashingKeeper:   slashingKeeper,
		feeCollectorName: feeCollectorName,
	}
}

// Logger returns a module-specific logger.
func (k Keeper) Logger(ctx sdk.Context) log.Logger {
	return ctx.Logger().With("module", "x/"+host.ModuleName+"-"+types.ModuleName)
}

// IsBound checks if the CCV module is already bound to the desired port
func (k Keeper) IsBound(ctx sdk.Context, portID string) bool {
	_, ok := k.scopedKeeper.GetCapability(ctx, host.PortPath(portID))
	return ok
}

// BindPort defines a wrapper function for the port Keeper's function in
// order to expose it to module's InitGenesis function
func (k Keeper) BindPort(ctx sdk.Context, portID string) error {
	cap := k.portKeeper.BindPort(ctx, portID)
	return k.ClaimCapability(ctx, cap, host.PortPath(portID))
}

// GetPort returns the portID for the CCV module. Used in ExportGenesis
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

// ClaimCapability allows the transfer module that can claim a capability that IBC module
// passes to it
func (k Keeper) ClaimCapability(ctx sdk.Context, cap *capabilitytypes.Capability, name string) error {
	return k.scopedKeeper.ClaimCapability(ctx, cap, name)
}

// SetChainToChannel sets the mapping from a consumer chainID to the CCV channel ID for that consumer chain.
func (k Keeper) SetChainToChannel(ctx sdk.Context, chainID, channelID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ChainToChannelKey(chainID), []byte(channelID))
}

// GetChainToChannel gets the CCV channelID for the given consumer chainID
func (k Keeper) GetChainToChannel(ctx sdk.Context, chainID string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ChainToChannelKey(chainID))
	if bz == nil {
		return "", false
	}
	return string(bz), true
}

// DeleteChainToChannel deletes the CCV channel ID for the given consumer chain ID
func (k Keeper) DeleteChainToChannel(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ChainToChannelKey(chainID))
}

// IterateConsumerChains iterates over all of the consumer chains that the provider module controls
// It calls the provided callback function which takes in a chainID and client ID to return
// a stop boolean which will stop the iteration.
func (k Keeper) IterateConsumerChains(ctx sdk.Context, cb func(ctx sdk.Context, chainID, clientID string) (stop bool)) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ChainToClientBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// remove 1 byte prefix from key to retrieve chainID
		chainID := string(iterator.Key()[1:])
		clientID := string(iterator.Value())

		if !cb(ctx, chainID, clientID) {
			return
		}
	}
}

// SetChannelToChain sets the mapping from the CCV channel ID to the consumer chainID.
func (k Keeper) SetChannelToChain(ctx sdk.Context, channelID, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ChannelToChainKey(channelID), []byte(chainID))
}

// GetChannelToChain gets the consumer chainID for a given CCV channelID
func (k Keeper) GetChannelToChain(ctx sdk.Context, channelID string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ChannelToChainKey(channelID))
	if bz == nil {
		return "", false
	}
	return string(bz), true
}

// DeleteChannelToChain deletes the consumer chain ID for a given CCV channe lID
func (k Keeper) DeleteChannelToChain(ctx sdk.Context, channelID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ChannelToChainKey(channelID))
}

// IterateChannelToChain iterates over the channel to chain mappings and calls the provided callback until the iteration ends
// or the callback returns stop=true
func (k Keeper) IterateChannelToChain(ctx sdk.Context, cb func(ctx sdk.Context, channelID, chainID string) (stop bool)) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ChannelToChainBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// remove prefix from key to retrieve channelID
		channelID := string(iterator.Key()[1:])

		chainID := string(iterator.Value())

		if cb(ctx, channelID, chainID) {
			break
		}
	}
}

func (k Keeper) SetConsumerGenesis(ctx sdk.Context, chainID string, gen consumertypes.GenesisState) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := gen.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.ConsumerGenesisKey(chainID), bz)

	return nil
}

func (k Keeper) GetConsumerGenesis(ctx sdk.Context, chainID string) (consumertypes.GenesisState, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerGenesisKey(chainID))
	if bz == nil {
		return consumertypes.GenesisState{}, false
	}

	var data consumertypes.GenesisState
	if err := data.Unmarshal(bz); err != nil {
		panic(fmt.Errorf("consumer genesis could not be unmarshaled: %w", err))
	}
	return data, true
}

func (k Keeper) DeleteConsumerGenesis(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerGenesisKey(chainID))
}

// VerifyConsumerChain verifies that the chain trying to connect on the channel handshake
// is the expected consumer chain.
func (k Keeper) VerifyConsumerChain(ctx sdk.Context, channelID string, connectionHops []string) error {
	if len(connectionHops) != 1 {
		return sdkerrors.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to provider chain")
	}
	connectionID := connectionHops[0]
	clientID, tmClient, err := k.getUnderlyingClient(ctx, connectionID)
	if err != nil {
		return err
	}
	ccvClientId, found := k.GetConsumerClientId(ctx, tmClient.ChainId)
	if !found {
		return sdkerrors.Wrapf(ccv.ErrClientNotFound, "cannot find client for consumer chain %s", tmClient.ChainId)
	}
	if ccvClientId != clientID {
		return sdkerrors.Wrapf(ccv.ErrInvalidConsumerClient, "CCV channel must be built on top of CCV client. expected %s, got %s", ccvClientId, clientID)
	}

	// Verify that there isn't already a CCV channel for the consumer chain
	if prevChannel, ok := k.GetChainToChannel(ctx, tmClient.ChainId); ok {
		return sdkerrors.Wrapf(ccv.ErrDuplicateChannel, "CCV channel with ID: %s already created for consumer chain %s", prevChannel, tmClient.ChainId)
	}
	return nil
}

// SetConsumerChain ensures that the consumer chain has not already been
// set by a different channel, and then sets the consumer chain mappings
// in keeper, and set the channel status to validating.
// If there is already a CCV channel between the provider and consumer
// chain then close the channel, so that another channel can be made.
//
// SetConsumerChain is called by OnChanOpenConfirm.
func (k Keeper) SetConsumerChain(ctx sdk.Context, channelID string) error {
	channel, ok := k.channelKeeper.GetChannel(ctx, ccv.ProviderPortID, channelID)
	if !ok {
		return sdkerrors.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for channel ID: %s", channelID)
	}
	if len(channel.ConnectionHops) != 1 {
		return sdkerrors.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to consumer chain")
	}
	connectionID := channel.ConnectionHops[0]
	_, tmClient, err := k.getUnderlyingClient(ctx, connectionID)
	if err != nil {
		return err
	}
	// Verify that there isn't already a CCV channel for the consumer chain
	chainID := tmClient.ChainId
	if prevChannelID, ok := k.GetChainToChannel(ctx, chainID); ok {
		return sdkerrors.Wrapf(ccv.ErrDuplicateChannel, "CCV channel with ID: %s already created for consumer chain %s", prevChannelID, chainID)
	}

	// the CCV channel is established:
	// - set channel mappings
	k.SetChainToChannel(ctx, chainID, channelID)
	k.SetChannelToChain(ctx, channelID, chainID)
	// - set current block height for the consumer chain initialization
	k.SetInitChainHeight(ctx, chainID, uint64(ctx.BlockHeight()))
	// - remove init timeout timestamp
	k.DeleteInitTimeoutTimestamp(ctx, chainID)
	return nil
}

// Save UnbondingOp by unique ID
func (k Keeper) SetUnbondingOp(ctx sdk.Context, unbondingOp ccv.UnbondingOp) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := unbondingOp.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.UnbondingOpKey(unbondingOp.Id), bz)
	return nil
}

// Get UnbondingOp by unique ID
func (k Keeper) GetUnbondingOp(ctx sdk.Context, id uint64) (ccv.UnbondingOp, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.UnbondingOpKey(id))
	if bz == nil {
		return ccv.UnbondingOp{}, false
	}

	return types.MustUnmarshalUnbondingOp(k.cdc, bz), true
}

func (k Keeper) DeleteUnbondingOp(ctx sdk.Context, id uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.UnbondingOpKey(id))
}

func (k Keeper) IterateOverUnbondingOps(ctx sdk.Context, cb func(id uint64, ubdOp ccv.UnbondingOp) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.UnbondingOpBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		id := binary.BigEndian.Uint64(iterator.Key()[1:])
		bz := iterator.Value()
		if bz == nil {
			panic(fmt.Errorf("unbonding operation is nil for id %d", id))
		}
		ubdOp := types.MustUnmarshalUnbondingOp(k.cdc, bz)

		if !cb(id, ubdOp) {
			break
		}
	}
}

// This index allows retreiving UnbondingDelegationEntries by chainID and valsetUpdateID
func (k Keeper) SetUnbondingOpIndex(ctx sdk.Context, chainID string, valsetUpdateID uint64, IDs []uint64) {
	store := ctx.KVStore(k.storeKey)

	index := ccv.UnbondingOpsIndex{
		Ids: IDs,
	}
	bz, err := index.Marshal()
	if err != nil {
		panic("Failed to marshal UnbondingOpsIndex")
	}

	store.Set(types.UnbondingOpIndexKey(chainID, valsetUpdateID), bz)
}

// IterateOverUnbondingOpIndex iterates over the unbonding indexes for a given chain id.
func (k Keeper) IterateOverUnbondingOpIndex(ctx sdk.Context, chainID string, cb func(vscID uint64, ubdIndex []uint64) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.UnbondingOpIndexBytePrefix, chainID))
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// parse key to get the current VSC ID
		_, vscID, err := types.ParseUnbondingOpIndexKey(iterator.Key())
		if err != nil {
			panic(fmt.Errorf("failed to parse UnbondingOpIndexKey: %w", err))
		}

		var index ccv.UnbondingOpsIndex
		if err = index.Unmarshal(iterator.Value()); err != nil {
			panic("Failed to unmarshal JSON")
		}

		if !cb(vscID, index.GetIds()) {
			return
		}
	}
}

// This index allows retrieving UnbondingDelegationEntries by chainID and valsetUpdateID
func (k Keeper) GetUnbondingOpIndex(ctx sdk.Context, chainID string, valsetUpdateID uint64) ([]uint64, bool) {
	store := ctx.KVStore(k.storeKey)

	bz := store.Get(types.UnbondingOpIndexKey(chainID, valsetUpdateID))
	if bz == nil {
		return []uint64{}, false
	}

	var idx ccv.UnbondingOpsIndex
	if err := idx.Unmarshal(bz); err != nil {
		panic("Failed to unmarshal UnbondingOpsIndex")
	}

	return idx.GetIds(), true
}

// This index allows retreiving UnbondingDelegationEntries by chainID and valsetUpdateID
func (k Keeper) DeleteUnbondingOpIndex(ctx sdk.Context, chainID string, valsetUpdateID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.UnbondingOpIndexKey(chainID, valsetUpdateID))
}

// Retrieve UnbondingDelegationEntries by chainID and valsetUpdateID
func (k Keeper) GetUnbondingOpsFromIndex(ctx sdk.Context, chainID string, valsetUpdateID uint64) (entries []ccv.UnbondingOp, found bool) {
	ids, found := k.GetUnbondingOpIndex(ctx, chainID, valsetUpdateID)
	if !found {
		return entries, false
	}
	for _, id := range ids {
		entry, found := k.GetUnbondingOp(ctx, id)
		if !found {
			// TODO JEHAN: is this the correct way to deal with this?
			panic("did not find UnbondingOp according to index- index was probably not correctly updated")
		}
		entries = append(entries, entry)
	}

	return entries, true
}

// GetMaturedUnbondingOps returns the list of matured unbonding operation ids
func (k Keeper) GetMaturedUnbondingOps(ctx sdk.Context) (ids []uint64, err error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.MaturedUnbondingOpsKey())
	if bz == nil {
		return nil, nil
	}

	var ops ccv.MaturedUnbondingOps
	if err := ops.Unmarshal(bz); err != nil {
		return nil, err
	}
	return ops.GetIds(), nil
}

// AppendMaturedUnbondingOps adds a list of ids to the list of matured unbonding operation ids
func (k Keeper) AppendMaturedUnbondingOps(ctx sdk.Context, ids []uint64) error {
	if len(ids) == 0 {
		return nil
	}
	existingIds, err := k.GetMaturedUnbondingOps(ctx)
	if err != nil {
		return err
	}

	maturedOps := ccv.MaturedUnbondingOps{
		Ids: append(existingIds, ids...),
	}

	store := ctx.KVStore(k.storeKey)
	bz, err := maturedOps.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.MaturedUnbondingOpsKey(), bz)
	return nil
}

// ConsumeMaturedUnbondingOps empties and returns list of matured unbonding operation ids (if it exists)
func (k Keeper) ConsumeMaturedUnbondingOps(ctx sdk.Context) ([]uint64, error) {
	ids, err := k.GetMaturedUnbondingOps(ctx)
	if err != nil {
		return nil, err
	}
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.MaturedUnbondingOpsKey())
	return ids, nil
}

// Retrieves the underlying client state corresponding to a connection ID.
func (k Keeper) getUnderlyingClient(ctx sdk.Context, connectionID string) (
	clientID string, tmClient *ibctmtypes.ClientState, err error) {

	conn, ok := k.connectionKeeper.GetConnection(ctx, connectionID)
	if !ok {
		return "", nil, sdkerrors.Wrapf(conntypes.ErrConnectionNotFound,
			"connection not found for connection ID: %s", connectionID)
	}
	clientID = conn.ClientId
	clientState, ok := k.clientKeeper.GetClientState(ctx, clientID)
	if !ok {
		return "", nil, sdkerrors.Wrapf(clienttypes.ErrClientNotFound,
			"client not found for client ID: %s", conn.ClientId)
	}
	tmClient, ok = clientState.(*ibctmtypes.ClientState)
	if !ok {
		return "", nil, sdkerrors.Wrapf(clienttypes.ErrInvalidClientType,
			"invalid client type. expected %s, got %s", ibcexported.Tendermint, clientState.ClientType())
	}
	return clientID, tmClient, nil
}

// chanCloseInit defines a wrapper function for the channel Keeper's function
func (k Keeper) chanCloseInit(ctx sdk.Context, channelID string) error {
	capName := host.ChannelCapabilityPath(ccv.ProviderPortID, channelID)
	chanCap, ok := k.scopedKeeper.GetCapability(ctx, capName)
	if !ok {
		return sdkerrors.Wrapf(channeltypes.ErrChannelCapabilityNotFound, "could not retrieve channel capability at: %s", capName)
	}
	return k.channelKeeper.ChanCloseInit(ctx, ccv.ProviderPortID, channelID, chanCap)
}

func (k Keeper) IncrementValidatorSetUpdateId(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)

	// Unmarshal and increment
	validatorSetUpdateId := k.GetValidatorSetUpdateId(ctx)
	validatorSetUpdateId = validatorSetUpdateId + 1

	// Convert back into bytes for storage
	bz := make([]byte, 8)
	binary.BigEndian.PutUint64(bz, validatorSetUpdateId)

	store.Set(types.ValidatorSetUpdateIdKey(), bz)
}

func (k Keeper) SetValidatorSetUpdateId(ctx sdk.Context, valUpdateID uint64) {
	store := ctx.KVStore(k.storeKey)

	// Convert back into bytes for storage
	bz := make([]byte, 8)
	binary.BigEndian.PutUint64(bz, valUpdateID)

	store.Set(types.ValidatorSetUpdateIdKey(), bz)
}

func (k Keeper) GetValidatorSetUpdateId(ctx sdk.Context) (validatorSetUpdateId uint64) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ValidatorSetUpdateIdKey())

	if bz == nil {
		validatorSetUpdateId = 0
	} else {
		// Unmarshal
		validatorSetUpdateId = binary.BigEndian.Uint64(bz)
	}

	return validatorSetUpdateId
}

// SetValsetUpdateBlockHeight sets the block height for a given valset update id
func (k Keeper) SetValsetUpdateBlockHeight(ctx sdk.Context, valsetUpdateId, blockHeight uint64) {
	store := ctx.KVStore(k.storeKey)
	heightBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(heightBytes, blockHeight)
	store.Set(types.ValsetUpdateBlockHeightKey(valsetUpdateId), heightBytes)
}

// GetValsetUpdateBlockHeight gets the block height for a given valset update id
func (k Keeper) GetValsetUpdateBlockHeight(ctx sdk.Context, valsetUpdateId uint64) (uint64, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ValsetUpdateBlockHeightKey(valsetUpdateId))
	if bz == nil {
		return 0, false
	}
	return binary.BigEndian.Uint64(bz), true
}

// IterateSlashAcks iterates through the slash acks set in the store
func (k Keeper) IterateValsetUpdateBlockHeight(ctx sdk.Context, cb func(valsetUpdateId, height uint64) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ValsetUpdateBlockHeightBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {

		valsetUpdateId := binary.BigEndian.Uint64(iterator.Key()[1:])
		height := binary.BigEndian.Uint64(iterator.Value())

		if !cb(valsetUpdateId, height) {
			return
		}
	}
}

// DeleteValsetUpdateBlockHeight deletes the block height value for a given vaset update id
func (k Keeper) DeleteValsetUpdateBlockHeight(ctx sdk.Context, valsetUpdateId uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValsetUpdateBlockHeightKey(valsetUpdateId))
}

// SetSlashAcks sets the slash acks under the given chain ID
func (k Keeper) SetSlashAcks(ctx sdk.Context, chainID string, acks []string) {
	store := ctx.KVStore(k.storeKey)

	sa := types.SlashAcks{
		Addresses: acks,
	}
	bz, err := sa.Marshal()
	if err != nil {
		panic("failed to marshal SlashAcks")
	}
	store.Set(types.SlashAcksKey(chainID), bz)
}

// GetSlashAcks returns the slash acks stored under the given chain ID
func (k Keeper) GetSlashAcks(ctx sdk.Context, chainID string) []string {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.SlashAcksKey(chainID))
	if bz == nil {
		return nil
	}
	var acks types.SlashAcks
	if err := acks.Unmarshal(bz); err != nil {
		panic(fmt.Errorf("failed to decode json: %w", err))
	}

	return acks.GetAddresses()
}

// ConsumeSlashAcks empties and returns the slash acks for a given chain ID
func (k Keeper) ConsumeSlashAcks(ctx sdk.Context, chainID string) (acks []string) {
	acks = k.GetSlashAcks(ctx, chainID)
	if len(acks) < 1 {
		return
	}
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.SlashAcksKey(chainID))
	return
}

// IterateSlashAcks iterates through the slash acks set in the store
func (k Keeper) IterateSlashAcks(ctx sdk.Context, cb func(chainID string, acks []string) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.SlashAcksBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {

		chainID := string(iterator.Key()[1:])

		var sa types.SlashAcks
		err := sa.Unmarshal(iterator.Value())
		if err != nil {
			panic(fmt.Errorf("failed to unmarshal SlashAcks: %w", err))
		}

		if !cb(chainID, sa.GetAddresses()) {
			return
		}
	}
}

// AppendSlashAck appends the given slash ack to the given chain ID slash acks in store
func (k Keeper) AppendSlashAck(ctx sdk.Context, chainID, ack string) {
	acks := k.GetSlashAcks(ctx, chainID)
	acks = append(acks, ack)
	k.SetSlashAcks(ctx, chainID, acks)
}

// SetInitChainHeight sets the provider block height when the given consumer chain was initiated
func (k Keeper) SetInitChainHeight(ctx sdk.Context, chainID string, height uint64) {
	store := ctx.KVStore(k.storeKey)
	heightBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(heightBytes, height)

	store.Set(types.InitChainHeightKey(chainID), heightBytes)
}

// GetInitChainHeight returns the provider block height when the given consumer chain was initiated
func (k Keeper) GetInitChainHeight(ctx sdk.Context, chainID string) (uint64, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.InitChainHeightKey(chainID))
	if bz == nil {
		return 0, false
	}

	return binary.BigEndian.Uint64(bz), true
}

// DeleteInitChainHeight deletes the block height value for which the given consumer chain's channel was established
func (k Keeper) DeleteInitChainHeight(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.InitChainHeightKey(chainID))
}

// GetPendingVSCs returns the list of pending ValidatorSetChange packets stored under chain ID
func (k Keeper) GetPendingVSCs(ctx sdk.Context, chainID string) (packets []ccv.ValidatorSetChangePacketData, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingVSCsKey(chainID))
	if bz == nil {
		return nil, false
	}
	buf := bytes.NewBuffer(bz)

	var data [][]byte
	if err := json.NewDecoder(buf).Decode(&data); err != nil {
		panic(fmt.Errorf("pending validator set changes could not be decoded: %w", err))
	}

	for _, pdata := range data {
		var p ccv.ValidatorSetChangePacketData
		err := p.Unmarshal(pdata)
		if err != nil {
			panic("failed to unmarshal ValidatorSetChange packet data")
		}
		packets = append(packets, p)
	}

	return packets, true
}

// AppendPendingVSC adds the given ValidatorSetChange packet to the list
// of pending ValidatorSetChange packets stored under chain ID
func (k Keeper) AppendPendingVSC(ctx sdk.Context, chainID string, packet ccv.ValidatorSetChangePacketData) {
	packets, _ := k.GetPendingVSCs(ctx, chainID)
	// append works also on a nil list
	packets = append(packets, packet)

	store := ctx.KVStore(k.storeKey)
	var data [][]byte
	for _, p := range packets {
		pdata, err := p.Marshal()
		if err != nil {
			panic("failed to marshal ValidatorSetChange packet data")
		}
		data = append(data, pdata)
	}
	buf := &bytes.Buffer{}
	err := json.NewEncoder(buf).Encode(data)
	if err != nil {
		panic("failed to encode json")
	}
	store.Set(types.PendingVSCsKey(chainID), buf.Bytes())
}

// ConsumePendingVSCs empties and returns the list of pending ValidatorSetChange packets for chain ID (if it exists)
func (k Keeper) ConsumePendingVSCs(ctx sdk.Context, chainID string) (packets []ccv.ValidatorSetChangePacketData) {
	packets, found := k.GetPendingVSCs(ctx, chainID)
	if !found {
		// there is no list of pending ValidatorSetChange packets
		return nil
	}
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PendingVSCsKey(chainID))
	return packets
}

// GetLockUnbondingOnTimeout returns the mapping from the given consumer chain ID to a boolean value indicating whether
// the unbonding operation funds should be locked on CCV channel timeout
func (k Keeper) GetLockUnbondingOnTimeout(ctx sdk.Context, chainID string) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.LockUnbondingOnTimeoutKey(chainID))
	return bz != nil
}

// SetLockUnbondingOnTimeout locks the unbonding operation funds in case of a CCV channel timeouts for the given consumer chain ID
func (k Keeper) SetLockUnbondingOnTimeout(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.LockUnbondingOnTimeoutKey(chainID), []byte{})
}

// DeleteLockUnbondingOnTimeout deletes the unbonding operation lock in case of a CCV channel timeouts for the given consumer chain ID
func (k Keeper) DeleteLockUnbondingOnTimeout(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.LockUnbondingOnTimeoutKey(chainID))
}

// SetConsumerClientId sets the client ID for the given chain ID
func (k Keeper) SetConsumerClientId(ctx sdk.Context, chainID, clientID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ChainToClientKey(chainID), []byte(clientID))
}

// GetConsumerClientId returns the client ID for the given chain ID.
func (k Keeper) GetConsumerClientId(ctx sdk.Context, chainID string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	clientIdBytes := store.Get(types.ChainToClientKey(chainID))
	if clientIdBytes == nil {
		return "", false
	}
	return string(clientIdBytes), true
}

// DeleteConsumerClientId removes from the store the clientID for the given chainID.
func (k Keeper) DeleteConsumerClientId(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ChainToClientKey(chainID))
}

// SetInitTimeoutTimestamp sets the init timeout timestamp for the given chain ID
func (k Keeper) SetInitTimeoutTimestamp(ctx sdk.Context, chainID string, ts uint64) {
	store := ctx.KVStore(k.storeKey)
	tsBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(tsBytes, ts)
	store.Set(types.InitTimeoutTimestampKey(chainID), tsBytes)
}

// GetInitTimeoutTimestamp returns the init timeout timestamp for the given chain ID.
// This method is used only in testing.
func (k Keeper) GetInitTimeoutTimestamp(ctx sdk.Context, chainID string) (uint64, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.InitTimeoutTimestampKey(chainID))
	if bz == nil {
		return 0, false
	}
	return binary.BigEndian.Uint64(bz), true
}

// DeleteInitTimeoutTimestamp removes from the store the init timeout timestamp for the given chainID.
func (k Keeper) DeleteInitTimeoutTimestamp(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.InitTimeoutTimestampKey(chainID))
}

// IterateInitTimeoutTimestamp iterates through the init timeout timestamps in the store
func (k Keeper) IterateInitTimeoutTimestamp(ctx sdk.Context, cb func(chainID string, ts uint64) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.InitTimeoutTimestampBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		chainID := string(iterator.Key()[1:])
		ts := binary.BigEndian.Uint64(iterator.Value())
		if !cb(chainID, ts) {
			return
		}
	}
}

// SetVscSendTimestamp sets the VSC send timestamp
// for a VSCPacket with ID vscID sent to a chain with ID chainID
func (k Keeper) SetVscSendTimestamp(
	ctx sdk.Context,
	chainID string,
	vscID uint64,
	timestamp time.Time,
) {
	store := ctx.KVStore(k.storeKey)

	// Convert timestamp into bytes for storage
	timeBz := sdk.FormatTimeBytes(timestamp)

	store.Set(types.VscSendingTimestampKey(chainID, vscID), timeBz)
}

// DeleteVscSendTimestamp removes from the store a specific VSC send timestamp
// for the given chainID and vscID.
func (k Keeper) DeleteVscSendTimestamp(ctx sdk.Context, chainID string, vscID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.VscSendingTimestampKey(chainID, vscID))
}

// IterateVscSendTimestamps iterates in order (lowest first)
// over the vsc send timestamps of the given chainID.
func (k Keeper) IterateVscSendTimestamps(
	ctx sdk.Context,
	chainID string,
	cb func(vscID uint64, ts time.Time) bool,
) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.VscSendTimestampBytePrefix, chainID))
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		key := iterator.Key()
		_, vscID, err := types.ParseVscSendingTimestampKey(key)
		if err != nil {
			panic(fmt.Errorf("failed to parse VscSendTimestampKey: %w", err))
		}
		ts, err := sdk.ParseTimeBytes(iterator.Value())
		if err != nil {
			panic(fmt.Errorf("failed to parse timestamp value: %w", err))
		}
		if !cb(vscID, ts) {
			return
		}
	}
}
