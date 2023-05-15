package keeper

import (
	"encoding/binary"
	"fmt"
	"reflect"
	"time"

	errorsmod "cosmossdk.io/errors"
	"github.com/cosmos/cosmos-sdk/codec"
	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v7/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v7/modules/core/24-host"
	ibcexported "github.com/cosmos/ibc-go/v7/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	"github.com/cometbft/cometbft/libs/log"
)

// Keeper defines the Cross-Chain Validation Provider Keeper
type Keeper struct {
	storeKey         storetypes.StoreKey
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
	evidenceKeeper   ccv.EvidenceKeeper
	feeCollectorName string
}

// NewKeeper creates a new provider Keeper instance
func NewKeeper(
	cdc codec.BinaryCodec, key storetypes.StoreKey, paramSpace paramtypes.Subspace, scopedKeeper ccv.ScopedKeeper,
	channelKeeper ccv.ChannelKeeper, portKeeper ccv.PortKeeper,
	connectionKeeper ccv.ConnectionKeeper, clientKeeper ccv.ClientKeeper,
	stakingKeeper ccv.StakingKeeper, slashingKeeper ccv.SlashingKeeper,
	accountKeeper ccv.AccountKeeper, evidenceKeeper ccv.EvidenceKeeper,
	feeCollectorName string,
) Keeper {
	// set KeyTable if it has not already been set
	if !paramSpace.HasKeyTable() {
		paramSpace = paramSpace.WithKeyTable(types.ParamKeyTable())
	}

	k := Keeper{
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
		evidenceKeeper:   evidenceKeeper,
		feeCollectorName: feeCollectorName,
	}

	k.mustValidateFields()
	return k
}

// Validates that the provider keeper is initialized with non-zero and
// non-nil values for all its fields. Otherwise this method will panic.
func (k Keeper) mustValidateFields() {
	// Ensures no fields are missed in this validation
	if reflect.ValueOf(k).NumField() != 13 {
		panic("number of fields in provider keeper is not 13")
	}

	ccv.PanicIfZeroOrNil(k.cdc, "cdc")                           // 1
	ccv.PanicIfZeroOrNil(k.storeKey, "storeKey")                 // 2
	ccv.PanicIfZeroOrNil(k.paramSpace, "paramSpace")             // 3
	ccv.PanicIfZeroOrNil(k.scopedKeeper, "scopedKeeper")         // 4
	ccv.PanicIfZeroOrNil(k.channelKeeper, "channelKeeper")       // 5
	ccv.PanicIfZeroOrNil(k.portKeeper, "portKeeper")             // 6
	ccv.PanicIfZeroOrNil(k.connectionKeeper, "connectionKeeper") // 7
	ccv.PanicIfZeroOrNil(k.accountKeeper, "accountKeeper")       // 8
	ccv.PanicIfZeroOrNil(k.clientKeeper, "clientKeeper")         // 9
	ccv.PanicIfZeroOrNil(k.stakingKeeper, "stakingKeeper")       // 10
	ccv.PanicIfZeroOrNil(k.slashingKeeper, "slashingKeeper")     // 11
	ccv.PanicIfZeroOrNil(k.evidenceKeeper, "evidenceKeeper")     // 12
	ccv.PanicIfZeroOrNil(k.feeCollectorName, "feeCollectorName") // 13
}

// Logger returns a module-specific logger.
func (k Keeper) Logger(ctx sdk.Context) log.Logger {
	return ctx.Logger().With("module", "x/"+ibcexported.ModuleName+"-"+types.ModuleName)
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

// GetAllConsumerChains gets all of the consumer chains, for which the provider module
// created IBC clients. Consumer chains with created clients are also referred to as registered.
//
// Note that the registered consumer chains are stored under keys with the following format:
// ChainToClientBytePrefix | chainID
// Thus, the returned array is in ascending order of chainIDs.
func (k Keeper) GetAllConsumerChains(ctx sdk.Context) (chains []types.Chain) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ChainToClientBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// remove 1 byte prefix from key to retrieve chainID
		chainID := string(iterator.Key()[1:])
		clientID := string(iterator.Value())

		chains = append(chains, types.Chain{
			ChainId:  chainID,
			ClientId: clientID,
		})
	}

	return chains
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

// DeleteChannelToChain deletes the consumer chain ID for a given CCV channelID
func (k Keeper) DeleteChannelToChain(ctx sdk.Context, channelID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ChannelToChainKey(channelID))
}

// GetAllChannelToChains gets all channel to chain mappings. If a mapping exists,
// then the CCV channel to that consumer chain is established.
//
// Note that mapping from CCV channel IDs to consumer chainIDs
// is stored under keys with the following format:
// ChannelToChainBytePrefix | channelID
// Thus, the returned array is in ascending order of channelIDs.
func (k Keeper) GetAllChannelToChains(ctx sdk.Context) (channels []types.ChannelToChain) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ChannelToChainBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// remove prefix from key to retrieve channelID
		channelID := string(iterator.Key()[1:])
		chainID := string(iterator.Value())

		channels = append(channels, types.ChannelToChain{
			ChannelId: channelID,
			ChainId:   chainID,
		})
	}

	return channels
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
		// An error here would indicate something is very wrong,
		// the ConsumerGenesis is assumed to be correctly serialized in SetConsumerGenesis.
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
		return errorsmod.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to provider chain")
	}
	connectionID := connectionHops[0]
	clientID, tmClient, err := k.getUnderlyingClient(ctx, connectionID)
	if err != nil {
		return err
	}
	ccvClientId, found := k.GetConsumerClientId(ctx, tmClient.ChainId)
	if !found {
		return errorsmod.Wrapf(ccv.ErrClientNotFound, "cannot find client for consumer chain %s", tmClient.ChainId)
	}
	if ccvClientId != clientID {
		return errorsmod.Wrapf(ccv.ErrInvalidConsumerClient, "CCV channel must be built on top of CCV client. expected %s, got %s", ccvClientId, clientID)
	}

	// Verify that there isn't already a CCV channel for the consumer chain
	if prevChannel, ok := k.GetChainToChannel(ctx, tmClient.ChainId); ok {
		return errorsmod.Wrapf(ccv.ErrDuplicateChannel, "CCV channel with ID: %s already created for consumer chain %s", prevChannel, tmClient.ChainId)
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
		return errorsmod.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for channel ID: %s", channelID)
	}
	if len(channel.ConnectionHops) != 1 {
		return errorsmod.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to consumer chain")
	}
	connectionID := channel.ConnectionHops[0]
	clientID, tmClient, err := k.getUnderlyingClient(ctx, connectionID)
	if err != nil {
		return err
	}
	// Verify that there isn't already a CCV channel for the consumer chain
	chainID := tmClient.ChainId
	if prevChannelID, ok := k.GetChainToChannel(ctx, chainID); ok {
		return errorsmod.Wrapf(ccv.ErrDuplicateChannel, "CCV channel with ID: %s already created for consumer chain %s", prevChannelID, chainID)
	}

	// the CCV channel is established:
	// - set channel mappings
	k.SetChainToChannel(ctx, chainID, channelID)
	k.SetChannelToChain(ctx, channelID, chainID)
	// - set current block height for the consumer chain initialization
	k.SetInitChainHeight(ctx, chainID, uint64(ctx.BlockHeight()))
	// - remove init timeout timestamp
	k.DeleteInitTimeoutTimestamp(ctx, chainID)

	// emit event on successful addition
	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypeChannelEstablished,
			sdk.NewAttribute(sdk.AttributeKeyModule, consumertypes.ModuleName),
			sdk.NewAttribute(ccv.AttributeChainID, chainID),
			sdk.NewAttribute(conntypes.AttributeKeyClientID, clientID),
			sdk.NewAttribute(channeltypes.AttributeKeyChannelID, channelID),
			sdk.NewAttribute(conntypes.AttributeKeyConnectionID, connectionID),
		),
	)
	return nil
}

// SetUnbondingOp sets the UnbondingOp by its unique ID
func (k Keeper) SetUnbondingOp(ctx sdk.Context, unbondingOp types.UnbondingOp) {
	store := ctx.KVStore(k.storeKey)
	bz, err := unbondingOp.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// unbondingOp is either instantiated in AfterUnbondingInitiated,
		// updated correctly by RemoveConsumerFromUnbondingOp,
		// or set during InitGenesis.
		panic(fmt.Errorf("unbonding op could not be marshaled: %w", err))
	}
	store.Set(types.UnbondingOpKey(unbondingOp.Id), bz)
}

// GetUnbondingOp gets a UnbondingOp by its unique ID
func (k Keeper) GetUnbondingOp(ctx sdk.Context, id uint64) (types.UnbondingOp, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.UnbondingOpKey(id))
	if bz == nil {
		return types.UnbondingOp{}, false
	}

	var unbondingOp types.UnbondingOp
	if err := unbondingOp.Unmarshal(bz); err != nil {
		// An error here would indicate something is very wrong,
		// the UnbondingOp is assumed to be correctly serialized in SetUnbondingOp.
		panic(fmt.Errorf("failed to unmarshal UnbondingOp: %w", err))
	}

	return unbondingOp, true
}

// DeleteUnbondingOp deletes a UnbondingOp given its ID
func (k Keeper) DeleteUnbondingOp(ctx sdk.Context, id uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.UnbondingOpKey(id))
}

// GetAllUnbondingOps gets all UnbondingOps, where each UnbondingOp consists
// of its unique ID and a list of consumer chainIDs that the unbonding operation
// is waiting on.
//
// Note that UnbondingOps are stored under keys with the following format:
// UnbondingOpBytePrefix | ID
// Thus, the iteration is in ascending order of IDs.
func (k Keeper) GetAllUnbondingOps(ctx sdk.Context) (ops []types.UnbondingOp) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.UnbondingOpBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		id := binary.BigEndian.Uint64(iterator.Key()[1:])
		bz := iterator.Value()
		if bz == nil {
			// An error here would indicate something is very wrong,
			// the UnbondingOp is assumed to be correctly set in SetUnbondingOp.
			panic(fmt.Errorf("unbonding operation is nil for id %d", id))
		}
		var unbondingOp types.UnbondingOp
		if err := unbondingOp.Unmarshal(bz); err != nil {
			// An error here would indicate something is very wrong,
			// the UnbondingOp is assumed to be correctly serialized in SetUnbondingOp.
			panic(fmt.Errorf("failed to unmarshal UnbondingOp: %w", err))
		}

		ops = append(ops, unbondingOp)
	}

	return ops
}

// RemoveConsumerFromUnbondingOp removes a consumer chain ID that the unbonding op with 'id' is waiting on.
// The method returns true if the unbonding op can complete. In this case the record is removed from store.
// The method panics if the unbonding op with 'id' is not found.
func (k Keeper) RemoveConsumerFromUnbondingOp(ctx sdk.Context, id uint64, chainID string) (canComplete bool) {
	// Get the unbonding op from store
	unbondingOp, found := k.GetUnbondingOp(ctx, id)
	if !found {
		panic(fmt.Errorf("internal state corrupted; could not find UnbondingOp with ID %d", id))
	}

	// Remove consumer chain ID from unbonding op
	var numRemoved int
	unbondingOp.UnbondingConsumerChains, numRemoved = removeStringFromSlice(unbondingOp.UnbondingConsumerChains, chainID)
	if numRemoved > 0 {
		k.Logger(ctx).Debug("unbonding operation matured on consumer", "chainID", chainID, "opID", id)

		if len(unbondingOp.UnbondingConsumerChains) == 0 {
			// Delete unbonding op
			k.DeleteUnbondingOp(ctx, id)
			// No more consumer chains; the unbonding op can complete
			canComplete = true
		} else {
			// Update unbonding op in store
			k.SetUnbondingOp(ctx, unbondingOp)
		}
	}
	return
}

func removeStringFromSlice(slice []string, x string) (newSlice []string, numRemoved int) {
	for _, y := range slice {
		if x != y {
			newSlice = append(newSlice, y)
		}
	}

	return newSlice, len(slice) - len(newSlice)
}

// SetUnbondingOpIndex sets the IDs of unbonding operations that are waiting for
// a VSCMaturedPacket with vscID from a consumer with chainID
func (k Keeper) SetUnbondingOpIndex(ctx sdk.Context, chainID string, vscID uint64, ids []uint64) {
	store := ctx.KVStore(k.storeKey)

	vscUnbondingOps := types.VscUnbondingOps{
		VscId:          vscID,
		UnbondingOpIds: ids,
	}
	bz, err := vscUnbondingOps.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// vscUnbondingOps is instantiated in this method and should be able to be marshaled.
		panic(fmt.Errorf("failed to marshal VscUnbondingOps: %w", err))
	}

	store.Set(types.UnbondingOpIndexKey(chainID, vscID), bz)
}

// GetAllUnbondingOpIndexes gets all unbonding indexes for a given chain id,
// i.e., all the IDs of unbonding operations that are waiting for
// VSCMaturedPackets from a consumer with chainID.
//
// Note that the unbonding indexes for a given chainID are stored under keys with the following format:
// UnbondingOpIndexBytePrefix | len(chainID) | chainID | vscID
// Thus, the returned array is in ascending order of vscIDs.
func (k Keeper) GetAllUnbondingOpIndexes(ctx sdk.Context, chainID string) (indexes []types.VscUnbondingOps) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.UnbondingOpIndexBytePrefix, chainID))
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var vscUnbondingOps types.VscUnbondingOps
		if err := vscUnbondingOps.Unmarshal(iterator.Value()); err != nil {
			// An error here would indicate something is very wrong,
			// the VscUnbondingOps are assumed to be correctly serialized in SetUnbondingOpIndex.
			panic(fmt.Errorf("failed to unmarshal VscUnbondingOps: %w", err))
		}

		indexes = append(indexes, types.VscUnbondingOps{
			VscId:          vscUnbondingOps.GetVscId(),
			UnbondingOpIds: vscUnbondingOps.GetUnbondingOpIds(),
		})
	}

	return indexes
}

// GetUnbondingOpIndex gets the IDs of unbonding operations that are waiting for
// a VSCMaturedPacket with vscID from a consumer with chainID
func (k Keeper) GetUnbondingOpIndex(ctx sdk.Context, chainID string, vscID uint64) ([]uint64, bool) {
	store := ctx.KVStore(k.storeKey)

	bz := store.Get(types.UnbondingOpIndexKey(chainID, vscID))
	if bz == nil {
		return []uint64{}, false
	}

	var vscUnbondingOps types.VscUnbondingOps
	if err := vscUnbondingOps.Unmarshal(bz); err != nil {
		// An error here would indicate something is very wrong,
		// the VscUnbondingOps are assumed to be correctly serialized in SetUnbondingOpIndex.
		panic(fmt.Errorf("failed to unmarshal VscUnbondingOps: %w", err))
	}

	return vscUnbondingOps.GetUnbondingOpIds(), true
}

// DeleteUnbondingOpIndex deletes the IDs of unbonding operations that are waiting for
// a VSCMaturedPacket with vscID from a consumer with chainID
func (k Keeper) DeleteUnbondingOpIndex(ctx sdk.Context, chainID string, vscID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.UnbondingOpIndexKey(chainID, vscID))
}

// GetUnbondingOpsFromIndex gets the unbonding ops waiting for a given chainID and vscID
func (k Keeper) GetUnbondingOpsFromIndex(ctx sdk.Context, chainID string, valsetUpdateID uint64) (entries []types.UnbondingOp) {
	ids, found := k.GetUnbondingOpIndex(ctx, chainID, valsetUpdateID)
	if !found {
		return entries
	}
	for _, id := range ids {
		entry, found := k.GetUnbondingOp(ctx, id)
		if !found {
			// An error here would indicate something is very wrong.
			// Every UnbondingOpIndex is assumed to have the corresponding UnbondingOps set in store.
			// This is done in AfterUnbondingInitiated and InitGenesis.
			panic("did not find UnbondingOp according to index- index was probably not correctly updated")
		}
		entries = append(entries, entry)
	}

	return entries
}

// GetMaturedUnbondingOps returns the list of matured unbonding operation ids
func (k Keeper) GetMaturedUnbondingOps(ctx sdk.Context) (ids []uint64) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.MaturedUnbondingOpsKey())
	if bz == nil {
		// Note that every call to ConsumeMaturedUnbondingOps
		// deletes the MaturedUnbondingOpsKey, which means that
		// the first call to GetMaturedUnbondingOps after that
		// will enter this branch.
		return nil
	}

	var ops ccv.MaturedUnbondingOps
	if err := ops.Unmarshal(bz); err != nil {
		// An error here would indicate something is very wrong,
		// the MaturedUnbondingOps are assumed to be correctly serialized in AppendMaturedUnbondingOps.
		panic(fmt.Errorf("failed to unmarshal MaturedUnbondingOps: %w", err))
	}
	return ops.GetIds()
}

// AppendMaturedUnbondingOps adds a list of ids to the list of matured unbonding operation ids
func (k Keeper) AppendMaturedUnbondingOps(ctx sdk.Context, ids []uint64) {
	if len(ids) == 0 {
		return
	}
	existingIds := k.GetMaturedUnbondingOps(ctx)
	maturedOps := ccv.MaturedUnbondingOps{
		Ids: append(existingIds, ids...),
	}

	store := ctx.KVStore(k.storeKey)
	bz, err := maturedOps.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// maturedOps is instantiated in this method and should be able to be marshaled.
		panic(fmt.Sprintf("failed to marshal matured unbonding operations: %s", err))
	}
	store.Set(types.MaturedUnbondingOpsKey(), bz)
}

// ConsumeMaturedUnbondingOps empties and returns list of matured unbonding operation ids (if it exists)
func (k Keeper) ConsumeMaturedUnbondingOps(ctx sdk.Context) []uint64 {
	ids := k.GetMaturedUnbondingOps(ctx)
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.MaturedUnbondingOpsKey())
	return ids
}

// Retrieves the underlying client state corresponding to a connection ID.
func (k Keeper) getUnderlyingClient(ctx sdk.Context, connectionID string) (
	clientID string, tmClient *ibctmtypes.ClientState, err error,
) {
	conn, ok := k.connectionKeeper.GetConnection(ctx, connectionID)
	if !ok {
		return "", nil, errorsmod.Wrapf(conntypes.ErrConnectionNotFound,
			"connection not found for connection ID: %s", connectionID)
	}
	clientID = conn.ClientId
	clientState, ok := k.clientKeeper.GetClientState(ctx, clientID)
	if !ok {
		return "", nil, errorsmod.Wrapf(clienttypes.ErrClientNotFound,
			"client not found for client ID: %s", conn.ClientId)
	}
	tmClient, ok = clientState.(*ibctmtypes.ClientState)
	if !ok {
		return "", nil, errorsmod.Wrapf(clienttypes.ErrInvalidClientType,
			"invalid client type. expected %s, got %s", ibcexported.Tendermint, clientState.ClientType())
	}
	return clientID, tmClient, nil
}

// chanCloseInit defines a wrapper function for the channel Keeper's function
func (k Keeper) chanCloseInit(ctx sdk.Context, channelID string) error {
	capName := host.ChannelCapabilityPath(ccv.ProviderPortID, channelID)
	chanCap, ok := k.scopedKeeper.GetCapability(ctx, capName)
	if !ok {
		return errorsmod.Wrapf(channeltypes.ErrChannelCapabilityNotFound, "could not retrieve channel capability at: %s", capName)
	}
	return k.channelKeeper.ChanCloseInit(ctx, ccv.ProviderPortID, channelID, chanCap)
}

func (k Keeper) IncrementValidatorSetUpdateId(ctx sdk.Context) {
	validatorSetUpdateId := k.GetValidatorSetUpdateId(ctx)
	k.SetValidatorSetUpdateId(ctx, validatorSetUpdateId+1)
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

// GetAllValsetUpdateBlockHeights gets all the block heights for all valset updates
//
// Note that the mapping from vscIDs to block heights is stored under keys with the following format:
// ValsetUpdateBlockHeightBytePrefix | vscID
// Thus, the returned array is in ascending order of vscIDs.
func (k Keeper) GetAllValsetUpdateBlockHeights(ctx sdk.Context) (valsetUpdateBlockHeights []types.ValsetUpdateIdToHeight) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ValsetUpdateBlockHeightBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		valsetUpdateId := binary.BigEndian.Uint64(iterator.Key()[1:])
		height := binary.BigEndian.Uint64(iterator.Value())

		valsetUpdateBlockHeights = append(valsetUpdateBlockHeights, types.ValsetUpdateIdToHeight{
			ValsetUpdateId: valsetUpdateId,
			Height:         height,
		})
	}

	return valsetUpdateBlockHeights
}

// DeleteValsetUpdateBlockHeight deletes the block height value for a given vaset update id
func (k Keeper) DeleteValsetUpdateBlockHeight(ctx sdk.Context, valsetUpdateId uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValsetUpdateBlockHeightKey(valsetUpdateId))
}

// SetSlashAcks sets the slash acks under the given chain ID
//
// TODO: SlashAcks should be persisted as a list of ConsumerConsAddr types, not strings.
// See https://github.com/cosmos/interchain-security/issues/728
func (k Keeper) SetSlashAcks(ctx sdk.Context, chainID string, acks []string) {
	store := ctx.KVStore(k.storeKey)

	sa := types.SlashAcks{
		Addresses: acks,
	}
	bz, err := sa.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// sa is instantiated in this method and should be able to be marshaled.
		panic(fmt.Errorf("failed to marshal SlashAcks: %w", err))
	}
	store.Set(types.SlashAcksKey(chainID), bz)
}

// GetSlashAcks returns the slash acks stored under the given chain ID
//
// TODO: SlashAcks should be persisted as a list of ConsumerConsAddr types, not strings.
// See https://github.com/cosmos/interchain-security/issues/728
func (k Keeper) GetSlashAcks(ctx sdk.Context, chainID string) []string {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.SlashAcksKey(chainID))
	if bz == nil {
		return nil
	}
	var acks types.SlashAcks
	if err := acks.Unmarshal(bz); err != nil {
		// An error here would indicate something is very wrong,
		// the SlashAcks are assumed to be correctly serialized in SetSlashAcks.
		panic(fmt.Errorf("failed to unmarshal SlashAcks: %w", err))
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

// DeleteSlashAcks deletes the slash acks for a given chain ID
func (k Keeper) DeleteSlashAcks(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.SlashAcksKey(chainID))
}

// AppendSlashAck appends the given slash ack to the given chain ID slash acks in store
func (k Keeper) AppendSlashAck(ctx sdk.Context, chainID,
	ack string, // TODO: consumer cons addr should be accepted here, see https://github.com/cosmos/interchain-security/issues/728
) {
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

// GetPendingVSCPackets returns the list of pending ValidatorSetChange packets stored under chain ID
func (k Keeper) GetPendingVSCPackets(ctx sdk.Context, chainID string) []ccv.ValidatorSetChangePacketData {
	var packets ccv.ValidatorSetChangePackets

	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingVSCsKey(chainID))
	if bz == nil {
		return []ccv.ValidatorSetChangePacketData{}
	}
	if err := packets.Unmarshal(bz); err != nil {
		// An error here would indicate something is very wrong,
		// the PendingVSCPackets are assumed to be correctly serialized in AppendPendingVSCPackets.
		panic(fmt.Errorf("cannot unmarshal pending validator set changes: %w", err))
	}
	return packets.GetList()
}

// AppendPendingVSCPackets adds the given ValidatorSetChange packet to the list
// of pending ValidatorSetChange packets stored under chain ID
func (k Keeper) AppendPendingVSCPackets(ctx sdk.Context, chainID string, newPackets ...ccv.ValidatorSetChangePacketData) {
	pds := append(k.GetPendingVSCPackets(ctx, chainID), newPackets...)

	store := ctx.KVStore(k.storeKey)
	packets := ccv.ValidatorSetChangePackets{List: pds}
	buf, err := packets.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// packets is instantiated in this method and should be able to be marshaled.
		panic(fmt.Errorf("cannot marshal pending validator set changes: %w", err))
	}
	store.Set(types.PendingVSCsKey(chainID), buf)
}

// DeletePendingVSCPackets deletes the list of pending ValidatorSetChange packets for chain ID
func (k Keeper) DeletePendingVSCPackets(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PendingVSCsKey(chainID))
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

// GetAllInitTimeoutTimestamps gets all init timeout timestamps in the store.
//
// Note that the init timeout timestamps are stored under keys with the following format:
// InitTimeoutTimestampBytePrefix | chainID
// Thus, the returned array is in ascending order of chainIDs (NOT in timestamp order).
func (k Keeper) GetAllInitTimeoutTimestamps(ctx sdk.Context) (initTimeoutTimestamps []types.InitTimeoutTimestamp) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.InitTimeoutTimestampBytePrefix})

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		chainID := string(iterator.Key()[1:])
		ts := binary.BigEndian.Uint64(iterator.Value())

		initTimeoutTimestamps = append(initTimeoutTimestamps, types.InitTimeoutTimestamp{
			ChainId:   chainID,
			Timestamp: ts,
		})
	}

	return initTimeoutTimestamps
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

// GetVscSendTimestamp returns a VSC send timestamp by chainID and vscID
//
// Note: This method is used only for testing.
func (k Keeper) GetVscSendTimestamp(ctx sdk.Context, chainID string, vscID uint64) (time.Time, bool) {
	store := ctx.KVStore(k.storeKey)

	timeBz := store.Get(types.VscSendingTimestampKey(chainID, vscID))
	if timeBz == nil {
		return time.Time{}, false
	}

	ts, err := sdk.ParseTimeBytes(timeBz)
	if err != nil {
		return time.Time{}, false
	}
	return ts, true
}

// DeleteVscSendTimestamp removes from the store a specific VSC send timestamp
// for the given chainID and vscID.
func (k Keeper) DeleteVscSendTimestamp(ctx sdk.Context, chainID string, vscID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.VscSendingTimestampKey(chainID, vscID))
}

// GetAllVscSendTimestamps gets an array of all the vsc send timestamps of the given chainID.
//
// Note that the vsc send timestamps of a given chainID are stored under keys with the following format:
// VscSendTimestampBytePrefix | len(chainID) | chainID | vscID
// Thus, the iteration is in ascending order of vscIDs, and as a result in send timestamp order.
func (k Keeper) GetAllVscSendTimestamps(ctx sdk.Context, chainID string) (vscSendTimestamps []types.VscSendTimestamp) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.VscSendTimestampBytePrefix, chainID))
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		_, vscID, err := types.ParseVscSendingTimestampKey(iterator.Key())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the store key is assumed to be correctly serialized in SetVscSendTimestamp.
			panic(fmt.Errorf("failed to parse VscSendTimestampKey: %w", err))
		}
		ts, err := sdk.ParseTimeBytes(iterator.Value())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the timestamp is assumed to be correctly serialized in SetVscSendTimestamp.
			panic(fmt.Errorf("failed to parse timestamp value: %w", err))
		}

		vscSendTimestamps = append(vscSendTimestamps, types.VscSendTimestamp{
			VscId:     vscID,
			Timestamp: ts,
		})
	}

	return vscSendTimestamps
}

// DeleteVscSendTimestampsForConsumer deletes all VSC send timestamps for a given consumer chain
func (k Keeper) DeleteVscSendTimestampsForConsumer(ctx sdk.Context, consumerChainID string) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.VscSendTimestampBytePrefix, consumerChainID))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	// Delete data for this consumer
	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// GetFirstVscSendTimestamp gets the vsc send timestamp with the lowest vscID for the given chainID.
func (k Keeper) GetFirstVscSendTimestamp(ctx sdk.Context, chainID string) (vscSendTimestamp types.VscSendTimestamp, found bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.VscSendTimestampBytePrefix, chainID))
	defer iterator.Close()

	if iterator.Valid() {
		_, vscID, err := types.ParseVscSendingTimestampKey(iterator.Key())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the store key is assumed to be correctly serialized in SetVscSendTimestamp.
			panic(fmt.Errorf("failed to parse VscSendTimestampKey: %w", err))
		}
		ts, err := sdk.ParseTimeBytes(iterator.Value())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the timestamp is assumed to be correctly serialized in SetVscSendTimestamp.
			panic(fmt.Errorf("failed to parse timestamp value: %w", err))
		}

		return types.VscSendTimestamp{
			VscId:     vscID,
			Timestamp: ts,
		}, true
	}

	return types.VscSendTimestamp{}, false
}

// SetSlashLog updates validator's slash log for a consumer chain
// If an entry exists for a given validator address, at least one
// double signing slash packet was received by the provider from at least one consumer chain
func (k Keeper) SetSlashLog(
	ctx sdk.Context,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.SlashLogKey(providerAddr), []byte{})
}

// GetSlashLog returns a validator's slash log status
// True will be returned if an entry exists for a given validator address
func (k Keeper) GetSlashLog(
	ctx sdk.Context,
	providerAddr types.ProviderConsAddress,
) (found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.SlashLogKey(providerAddr))
	return bz != nil
}
