package keeper

import (
	"context"
	"encoding/binary"
	"fmt"
	"reflect"
	"time"

	addresscodec "cosmossdk.io/core/address"
	"cosmossdk.io/math"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v8/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v8/modules/core/24-host"
	ibchost "github.com/cosmos/ibc-go/v8/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"

	storetypes "cosmossdk.io/store/types"
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	capabilitytypes "github.com/cosmos/ibc-go/modules/capability/types"

	"cosmossdk.io/log"
	govkeeper "github.com/cosmos/cosmos-sdk/x/gov/keeper"

	consumertypes "github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// Keeper defines the Cross-Chain Validation Provider Keeper
type Keeper struct {
	// address capable of executing gov messages (gov module account)
	authority string

	storeKey storetypes.StoreKey

	cdc                codec.BinaryCodec
	scopedKeeper       ccv.ScopedKeeper
	channelKeeper      ccv.ChannelKeeper
	portKeeper         ccv.PortKeeper
	connectionKeeper   ccv.ConnectionKeeper
	accountKeeper      ccv.AccountKeeper
	clientKeeper       ccv.ClientKeeper
	stakingKeeper      ccv.StakingKeeper
	slashingKeeper     ccv.SlashingKeeper
	distributionKeeper ccv.DistributionKeeper
	bankKeeper         ccv.BankKeeper
	govKeeper          govkeeper.Keeper
	feeCollectorName   string

	validatorAddressCodec addresscodec.Codec
	consensusAddressCodec addresscodec.Codec
}

// NewKeeper creates a new provider Keeper instance
func NewKeeper(
	cdc codec.BinaryCodec, key storetypes.StoreKey, paramSpace paramtypes.Subspace, scopedKeeper ccv.ScopedKeeper,
	channelKeeper ccv.ChannelKeeper, portKeeper ccv.PortKeeper,
	connectionKeeper ccv.ConnectionKeeper, clientKeeper ccv.ClientKeeper,
	stakingKeeper ccv.StakingKeeper, slashingKeeper ccv.SlashingKeeper,
	accountKeeper ccv.AccountKeeper,
	distributionKeeper ccv.DistributionKeeper, bankKeeper ccv.BankKeeper,
	govKeeper govkeeper.Keeper,
	authority string,
	validatorAddressCodec, consensusAddressCodec addresscodec.Codec,
	feeCollectorName string,
) Keeper {
	k := Keeper{
		cdc:                   cdc,
		storeKey:              key,
		authority:             authority,
		scopedKeeper:          scopedKeeper,
		channelKeeper:         channelKeeper,
		portKeeper:            portKeeper,
		connectionKeeper:      connectionKeeper,
		clientKeeper:          clientKeeper,
		stakingKeeper:         stakingKeeper,
		slashingKeeper:        slashingKeeper,
		accountKeeper:         accountKeeper,
		distributionKeeper:    distributionKeeper,
		bankKeeper:            bankKeeper,
		feeCollectorName:      feeCollectorName,
		validatorAddressCodec: validatorAddressCodec,
		consensusAddressCodec: consensusAddressCodec,
		govKeeper:             govKeeper,
	}

	k.mustValidateFields()
	return k
}

// GetAuthority returns the x/ccv/provider module's authority.
func (k Keeper) GetAuthority() string {
	return k.authority
}

// ValidatorAddressCodec returns the app validator address codec.
func (k Keeper) ValidatorAddressCodec() addresscodec.Codec {
	return k.validatorAddressCodec
}

// ConsensusAddressCodec returns the app consensus address codec.
func (k Keeper) ConsensusAddressCodec() addresscodec.Codec {
	return k.consensusAddressCodec
}

// Validates that the provider keeper is initialized with non-zero and
// non-nil values for all its fields. Otherwise this method will panic.
func (k Keeper) mustValidateFields() {
	// Ensures no fields are missed in this validation
	if reflect.ValueOf(k).NumField() != 17 {
		panic(fmt.Sprintf("number of fields in provider keeper is not 18 - have %d", reflect.ValueOf(k).NumField()))
	}

	if k.validatorAddressCodec == nil || k.consensusAddressCodec == nil {
		panic("validator and/or consensus address codec are nil")
	}

	ccv.PanicIfZeroOrNil(k.cdc, "cdc")                                     // 1
	ccv.PanicIfZeroOrNil(k.storeKey, "storeKey")                           // 2
	ccv.PanicIfZeroOrNil(k.scopedKeeper, "scopedKeeper")                   // 3
	ccv.PanicIfZeroOrNil(k.channelKeeper, "channelKeeper")                 // 4
	ccv.PanicIfZeroOrNil(k.portKeeper, "portKeeper")                       // 5
	ccv.PanicIfZeroOrNil(k.connectionKeeper, "connectionKeeper")           // 6
	ccv.PanicIfZeroOrNil(k.accountKeeper, "accountKeeper")                 // 7
	ccv.PanicIfZeroOrNil(k.clientKeeper, "clientKeeper")                   // 8
	ccv.PanicIfZeroOrNil(k.stakingKeeper, "stakingKeeper")                 // 9
	ccv.PanicIfZeroOrNil(k.slashingKeeper, "slashingKeeper")               // 10
	ccv.PanicIfZeroOrNil(k.distributionKeeper, "distributionKeeper")       // 11
	ccv.PanicIfZeroOrNil(k.bankKeeper, "bankKeeper")                       // 12
	ccv.PanicIfZeroOrNil(k.feeCollectorName, "feeCollectorName")           // 13
	ccv.PanicIfZeroOrNil(k.authority, "authority")                         // 14
	ccv.PanicIfZeroOrNil(k.validatorAddressCodec, "validatorAddressCodec") // 15
	ccv.PanicIfZeroOrNil(k.consensusAddressCodec, "consensusAddressCodec") // 16

	// this can be nil in tests
	// ccv.PanicIfZeroOrNil(k.govKeeper, "govKeeper")                         // 17
}

func (k *Keeper) SetGovKeeper(govKeeper govkeeper.Keeper) {
	k.govKeeper = govKeeper
}

// Logger returns a module-specific logger.
func (k Keeper) Logger(ctx context.Context) log.Logger {
	sdkCtx := sdk.UnwrapSDKContext(ctx)
	return sdkCtx.Logger().With("module", "x/"+ibchost.ModuleName+"-"+types.ModuleName)
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

// SetConsumerIdToChannelId sets the mapping from a consumer id to the CCV channel id for that consumer chain.
func (k Keeper) SetConsumerIdToChannelId(ctx sdk.Context, consumerId, channelId string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ConsumerIdToChannelIdKey(consumerId), []byte(channelId))
}

// GetConsumerIdToChannelId gets the CCV channelId for the given consumer id
func (k Keeper) GetConsumerIdToChannelId(ctx sdk.Context, consumerId string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToChannelIdKey(consumerId))
	if bz == nil {
		return "", false
	}
	return string(bz), true
}

// DeleteConsumerIdToChannelId deletes the CCV channel id for the given consumer id
func (k Keeper) DeleteConsumerIdToChannelId(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToChannelIdKey(consumerId))
}

// GetAllRegisteredConsumerIds gets all of the consumer chain IDs, for which the provider module
// created IBC clients. Consumer chains with created clients are also referred to as registered.
//
// Note that the registered consumer chains are stored under keys with the following format:
// ConsumerIdToClientIdKeyPrefix | consumerId
// Thus, the returned array is in ascending order of chainIDs.
func (k Keeper) GetAllRegisteredConsumerIds(ctx sdk.Context) []string {
	consumerIds := []string{}

	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ConsumerIdToClientIdKeyPrefix())
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// remove 1 byte prefix from key to retrieve consumerId
		consumerId := string(iterator.Key()[1:])
		consumerIds = append(consumerIds, consumerId)
	}

	return consumerIds
}

// SetChannelToConsumerId sets the mapping from the CCV channel id to the consumer id.
func (k Keeper) SetChannelToConsumerId(ctx sdk.Context, channelId, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ChannelToConsumerIdKey(channelId), []byte(consumerId))
}

// GetChannelIdToConsumerId gets the consumer id for a given CCV channel id
func (k Keeper) GetChannelIdToConsumerId(ctx sdk.Context, channelID string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ChannelToConsumerIdKey(channelID))
	if bz == nil {
		return "", false
	}
	return string(bz), true
}

// DeleteChannelIdToConsumerId deletes the consumer id for a given CCV channel id
func (k Keeper) DeleteChannelIdToConsumerId(ctx sdk.Context, channelId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ChannelToConsumerIdKey(channelId))
}

// GetAllChannelToConsumers gets all channel to chain mappings. If a mapping exists,
// then the CCV channel to that consumer chain is established.
//
// Note that mapping from CCV channel IDs to consumer IDs
// is stored under keys with the following format:
// ChannelIdToConsumerIdKeyPrefix | channelID
// Thus, the returned array is in ascending order of channelIDs.
func (k Keeper) GetAllChannelToConsumers(ctx sdk.Context) (channelsToConsumers []struct {
	ChannelId  string
	ConsumerId string
}) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ChannelIdToConsumerIdKeyPrefix())
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// remove prefix from key to retrieve channelID
		channelID := string(iterator.Key()[1:])
		consumerId := string(iterator.Value())

		channelsToConsumers = append(channelsToConsumers, struct {
			ChannelId  string
			ConsumerId string
		}{
			ChannelId:  channelID,
			ConsumerId: consumerId,
		})
	}

	return channelsToConsumers
}

func (k Keeper) SetConsumerGenesis(ctx sdk.Context, consumerId string, gen ccv.ConsumerGenesisState) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := gen.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.ConsumerGenesisKey(consumerId), bz)

	return nil
}

func (k Keeper) GetConsumerGenesis(ctx sdk.Context, consumerId string) (ccv.ConsumerGenesisState, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerGenesisKey(consumerId))
	if bz == nil {
		return ccv.ConsumerGenesisState{}, false
	}

	var data ccv.ConsumerGenesisState
	if err := data.Unmarshal(bz); err != nil {
		// An error here would indicate something is very wrong,
		// the ConsumerGenesis is assumed to be correctly serialized in SetConsumerGenesis.
		panic(fmt.Errorf("consumer genesis could not be unmarshaled: %w", err))
	}
	return data, true
}

func (k Keeper) DeleteConsumerGenesis(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerGenesisKey(consumerId))
}

// VerifyConsumerChain verifies that the chain trying to connect on the channel handshake
// is the expected consumer chain.
func (k Keeper) VerifyConsumerChain(ctx sdk.Context, channelID string, connectionHops []string) error {
	if len(connectionHops) != 1 {
		return errorsmod.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to provider chain")
	}
	connectionID := connectionHops[0]
	clientId, _, err := k.getUnderlyingClient(ctx, connectionID)
	if err != nil {
		return err
	}

	consumerId, found := k.GetClientIdToConsumerId(ctx, clientId)
	if !found {
		return errorsmod.Wrapf(ccv.ErrConsumerChainNotFound, "cannot find consumer id associated with client id: %s", clientId)
	}
	ccvClientId, found := k.GetConsumerClientId(ctx, consumerId)
	if !found {
		return errorsmod.Wrapf(ccv.ErrClientNotFound, "cannot find client for consumer chain %s", consumerId)
	}
	if ccvClientId != clientId {
		return errorsmod.Wrapf(types.ErrInvalidConsumerClient, "CCV channel must be built on top of CCV client. expected %s, got %s", ccvClientId, clientId)
	}

	// Verify that there isn't already a CCV channel for the consumer chain
	if prevChannel, ok := k.GetConsumerIdToChannelId(ctx, consumerId); ok {
		return errorsmod.Wrapf(ccv.ErrDuplicateChannel, "CCV channel with ID: %s already created for consumer chain %s", prevChannel, consumerId)
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
	consumerId, found := k.GetClientIdToConsumerId(ctx, clientID)
	if !found {
		return errorsmod.Wrapf(types.ErrNoConsumerId, "cannot find a consumer chain associated for this client: %s", clientID)
	}
	// Verify that there isn't already a CCV channel for the consumer chain
	chainID := tmClient.ChainId
	if prevChannelID, ok := k.GetConsumerIdToChannelId(ctx, consumerId); ok {
		return errorsmod.Wrapf(ccv.ErrDuplicateChannel, "CCV channel with ID: %s already created for consumer chain with id %s", prevChannelID, consumerId)
	}

	// the CCV channel is established:
	// - set channel mappings
	k.SetConsumerIdToChannelId(ctx, consumerId, channelID)
	k.SetChannelToConsumerId(ctx, channelID, consumerId)
	// - set current block height for the consumer chain initialization
	k.SetInitChainHeight(ctx, consumerId, uint64(ctx.BlockHeight()))

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
			"invalid client type. expected %s, got %s", ibchost.Tendermint, clientState.ClientType())
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
		return 0
	}
	return binary.BigEndian.Uint64(bz)
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
// ValsetUpdateBlockHeightKeyPrefix | vscID
// Thus, the returned array is in ascending order of vscIDs.
func (k Keeper) GetAllValsetUpdateBlockHeights(ctx sdk.Context) (valsetUpdateBlockHeights []types.ValsetUpdateIdToHeight) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ValsetUpdateBlockHeightKeyPrefix())

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
func (k Keeper) SetSlashAcks(ctx sdk.Context, consumerId string, acks []string) {
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
	store.Set(types.SlashAcksKey(consumerId), bz)
}

// GetSlashAcks returns the slash acks stored under the given consumer id
//
// TODO: SlashAcks should be persisted as a list of ConsumerConsAddr types, not strings.
// See https://github.com/cosmos/interchain-security/issues/728
func (k Keeper) GetSlashAcks(ctx sdk.Context, consumerId string) []string {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.SlashAcksKey(consumerId))
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

// ConsumeSlashAcks empties and returns the slash acks for a given consumer id
func (k Keeper) ConsumeSlashAcks(ctx sdk.Context, consumerId string) (acks []string) {
	acks = k.GetSlashAcks(ctx, consumerId)
	if len(acks) < 1 {
		return
	}
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.SlashAcksKey(consumerId))
	return
}

// DeleteSlashAcks deletes the slash acks for a given consumer id
func (k Keeper) DeleteSlashAcks(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.SlashAcksKey(consumerId))
}

// AppendSlashAck appends the given slash ack to the given consumer id slash acks in store
func (k Keeper) AppendSlashAck(ctx sdk.Context, consumerId,
	ack string, // TODO: consumer cons addr should be accepted here, see https://github.com/cosmos/interchain-security/issues/728
) {
	acks := k.GetSlashAcks(ctx, consumerId)
	acks = append(acks, ack)
	k.SetSlashAcks(ctx, consumerId, acks)
}

// SetInitChainHeight sets the provider block height when the given consumer chain was initiated
func (k Keeper) SetInitChainHeight(ctx sdk.Context, consumerId string, height uint64) {
	store := ctx.KVStore(k.storeKey)
	heightBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(heightBytes, height)

	store.Set(types.InitChainHeightKey(consumerId), heightBytes)
}

// GetInitChainHeight returns the provider block height when the given consumer chain was initiated
func (k Keeper) GetInitChainHeight(ctx sdk.Context, consumerId string) (uint64, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.InitChainHeightKey(consumerId))
	if bz == nil {
		return 0, false
	}

	return binary.BigEndian.Uint64(bz), true
}

// DeleteInitChainHeight deletes the block height value for which the given consumer chain's channel was established
func (k Keeper) DeleteInitChainHeight(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.InitChainHeightKey(consumerId))
}

// GetPendingVSCPackets returns the list of pending ValidatorSetChange packets stored under consumer id
func (k Keeper) GetPendingVSCPackets(ctx sdk.Context, consumerId string) []ccv.ValidatorSetChangePacketData {
	var packets types.ValidatorSetChangePackets

	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingVSCsKey(consumerId))
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
// of pending ValidatorSetChange packets stored under consumer id
func (k Keeper) AppendPendingVSCPackets(ctx sdk.Context, consumerId string, newPackets ...ccv.ValidatorSetChangePacketData) {
	pds := append(k.GetPendingVSCPackets(ctx, consumerId), newPackets...)

	store := ctx.KVStore(k.storeKey)
	packets := types.ValidatorSetChangePackets{List: pds}
	buf, err := packets.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// packets is instantiated in this method and should be able to be marshaled.
		panic(fmt.Errorf("cannot marshal pending validator set changes: %w", err))
	}
	store.Set(types.PendingVSCsKey(consumerId), buf)
}

// DeletePendingVSCPackets deletes the list of pending ValidatorSetChange packets for chain ID
func (k Keeper) DeletePendingVSCPackets(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PendingVSCsKey(consumerId))
}

// SetConsumerClientId sets the client id for the given consumer id.
// Note that the method also stores a reverse index that can be accessed
// by calling GetClientIdToConsumerId.
func (k Keeper) SetConsumerClientId(ctx sdk.Context, consumerId, clientId string) {
	store := ctx.KVStore(k.storeKey)

	if prevClientId, found := k.GetConsumerClientId(ctx, consumerId); found {
		// delete reverse index
		store.Delete(types.ClientIdToConsumerIdKey(prevClientId))
	}

	store.Set(types.ConsumerIdToClientIdKey(consumerId), []byte(clientId))

	// set the reverse index
	store.Set(types.ClientIdToConsumerIdKey(clientId), []byte(consumerId))
}

// GetConsumerClientId returns the client id for the given consumer id.
func (k Keeper) GetConsumerClientId(ctx sdk.Context, consumerId string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	clientIdBytes := store.Get(types.ConsumerIdToClientIdKey(consumerId))
	if clientIdBytes == nil {
		return "", false
	}
	return string(clientIdBytes), true
}

// GetClientIdToConsumerId returns the consumer id associated with this client id
func (k Keeper) GetClientIdToConsumerId(ctx sdk.Context, clientId string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	consumerIdBytes := store.Get(types.ClientIdToConsumerIdKey(clientId))
	if consumerIdBytes == nil {
		return "", false
	}
	return string(consumerIdBytes), true
}

// DeleteConsumerClientId removes from the store the client id for the given consumer id.
// Note that the method also removes the reverse index.
func (k Keeper) DeleteConsumerClientId(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)

	if clientId, found := k.GetConsumerClientId(ctx, consumerId); found {
		// delete reverse index
		store.Delete(types.ClientIdToConsumerIdKey(clientId))
	}

	store.Delete(types.ConsumerIdToClientIdKey(consumerId))
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

func (k Keeper) BondDenom(ctx sdk.Context) (string, error) {
	return k.stakingKeeper.BondDenom(ctx)
}

// GetAllActiveConsumerIds returns all the consumer ids of chains that are registered, initialized, or launched
func (k Keeper) GetAllActiveConsumerIds(ctx sdk.Context) []string {
	latestConsumerId, found := k.GetConsumerId(ctx)
	if !found {
		return []string{}
	}

	consumerIds := []string{}
	for i := uint64(0); i < latestConsumerId; i++ {
		consumerId := fmt.Sprintf("%d", i)
		if !k.IsConsumerActive(ctx, consumerId) {
			continue
		}
		consumerIds = append(consumerIds, consumerId)
	}

	return consumerIds
}

func (k Keeper) SetOptedIn(
	ctx sdk.Context,
	consumerId string,
	providerConsAddress types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.OptedInKey(consumerId, providerConsAddress), []byte{})
}

func (k Keeper) DeleteOptedIn(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.OptedInKey(consumerId, providerAddr))
}

func (k Keeper) IsOptedIn(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Get(types.OptedInKey(consumerId, providerAddr)) != nil
}

// GetAllOptedIn returns all the opted-in validators on chain `consumerId`
func (k Keeper) GetAllOptedIn(
	ctx sdk.Context,
	consumerId string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.OptedInKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// DeleteAllOptedIn deletes all the opted-in validators for chain with `consumerId`
func (k Keeper) DeleteAllOptedIn(
	ctx sdk.Context,
	consumerId string,
) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.OptedInKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)

	var keysToDel [][]byte
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}
}

// SetConsumerCommissionRate sets a per-consumer chain commission rate
// for the given validator address
func (k Keeper) SetConsumerCommissionRate(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
	commissionRate math.LegacyDec,
) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := commissionRate.Marshal()
	if err != nil {
		err = fmt.Errorf("consumer commission rate marshalling failed: %s", err)
		k.Logger(ctx).Error(err.Error())
		return err
	}

	store.Set(types.ConsumerCommissionRateKey(consumerId, providerAddr), bz)
	return nil
}

// GetConsumerCommissionRate returns the per-consumer commission rate set
// for the given validator address
func (k Keeper) GetConsumerCommissionRate(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) (math.LegacyDec, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerCommissionRateKey(consumerId, providerAddr))
	if bz == nil {
		return math.LegacyZeroDec(), false
	}

	cr := math.LegacyZeroDec()
	// handle error gracefully since it's called in BeginBlockRD
	if err := cr.Unmarshal(bz); err != nil {
		k.Logger(ctx).Error("consumer commission rate unmarshalling failed: %s", err)
		return cr, false
	}

	return cr, true
}

// GetAllCommissionRateValidators returns all the validator address
// that set a commission rate for the given consumer id
func (k Keeper) GetAllCommissionRateValidators(
	ctx sdk.Context,
	consumerId string,
) (addresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.ConsumerCommissionRateKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerAddr := types.NewProviderConsAddress(iterator.Key()[len(key):])
		addresses = append(addresses, providerAddr)
	}

	return addresses
}

// DeleteConsumerCommissionRate the per-consumer chain commission rate
// associated to the given validator address
func (k Keeper) DeleteConsumerCommissionRate(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerCommissionRateKey(consumerId, providerAddr))
}

// SetAllowlist allowlists validator with `providerAddr` address on chain `consumerId`
func (k Keeper) SetAllowlist(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.AllowlistKey(consumerId, providerAddr), []byte{})
}

// GetAllowList returns all allowlisted validators
func (k Keeper) GetAllowList(
	ctx sdk.Context,
	consumerId string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.AllowlistKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// IsAllowlisted returns `true` if validator with `providerAddr` has been allowlisted on chain `consumerId`
func (k Keeper) IsAllowlisted(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.AllowlistKey(consumerId, providerAddr))
	return bz != nil
}

// DeleteAllowlist deletes all allowlisted validators
func (k Keeper) DeleteAllowlist(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.AllowlistKeyPrefix(), consumerId))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// IsAllowlistEmpty returns `true` if no validator is allowlisted on chain `consumerId`
func (k Keeper) IsAllowlistEmpty(ctx sdk.Context, consumerId string) bool {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.AllowlistKeyPrefix(), consumerId))
	defer iterator.Close()

	return !iterator.Valid()
}

// UpdateAllowlist populates the allowlist store for the consumer chain with this consumer id
func (k Keeper) UpdateAllowlist(ctx sdk.Context, consumerId string, allowlist []string) {
	k.DeleteAllowlist(ctx, consumerId)
	for _, address := range allowlist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetAllowlist(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	}
}

// SetDenylist denylists validator with `providerAddr` address on chain `consumerId`
func (k Keeper) SetDenylist(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.DenylistKey(consumerId, providerAddr), []byte{})
}

// GetDenyList returns all denylisted validators
func (k Keeper) GetDenyList(
	ctx sdk.Context,
	consumerId string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.DenylistKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// IsDenylisted returns `true` if validator with `providerAddr` has been denylisted on chain `consumerId`
func (k Keeper) IsDenylisted(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.DenylistKey(consumerId, providerAddr))
	return bz != nil
}

// DeleteDenylist deletes all denylisted validators
func (k Keeper) DeleteDenylist(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.DenylistKeyPrefix(), consumerId))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// IsDenylistEmpty returns `true` if no validator is denylisted on chain `consumerId`
func (k Keeper) IsDenylistEmpty(ctx sdk.Context, consumerId string) bool {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.DenylistKeyPrefix(), consumerId))
	defer iterator.Close()

	return !iterator.Valid()
}

// UpdateDenylist populates the denylist store for the consumer chain with this consumer id
func (k Keeper) UpdateDenylist(ctx sdk.Context, consumerId string, denylist []string) {
	k.DeleteDenylist(ctx, consumerId)
	for _, address := range denylist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetDenylist(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	}
}

// SetMinimumPowerInTopN sets the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) SetMinimumPowerInTopN(
	ctx sdk.Context,
	consumerId string,
	power int64,
) {
	store := ctx.KVStore(k.storeKey)

	buf := make([]byte, 8)
	binary.BigEndian.PutUint64(buf, uint64(power))

	store.Set(types.MinimumPowerInTopNKey(consumerId), buf)
}

// GetMinimumPowerInTopN returns the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) GetMinimumPowerInTopN(
	ctx sdk.Context,
	consumerId string,
) (int64, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.MinimumPowerInTopNKey(consumerId))
	if buf == nil {
		return 0, false
	}
	return int64(binary.BigEndian.Uint64(buf)), true
}

// DeleteMinimumPowerInTopN removes the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) DeleteMinimumPowerInTopN(
	ctx sdk.Context,
	consumerId string,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.MinimumPowerInTopNKey(consumerId))
}

// UpdateMinimumPowerInTopN populates the minimum power in Top N for the consumer chain with this consumer id
func (k Keeper) UpdateMinimumPowerInTopN(ctx sdk.Context, consumerId string, oldTopN uint32, newTopN uint32) error {
	// if the top N changes, we need to update the new minimum power in top N
	if newTopN != oldTopN {
		if newTopN > 0 {
			// if the chain receives a non-zero top N value, store the minimum power in the top N
			bondedValidators, err := k.GetLastProviderConsensusActiveValidators(ctx)
			if err != nil {
				return err
			}
			minPower, err := k.ComputeMinPowerInTopN(ctx, bondedValidators, newTopN)
			if err != nil {
				return err
			}
			k.SetMinimumPowerInTopN(ctx, consumerId, minPower)
		} else {
			// if the chain receives a zero top N value, we delete the min power
			k.DeleteMinimumPowerInTopN(ctx, consumerId)
		}
	}

	return nil
}

func (k Keeper) UnbondingCanComplete(ctx sdk.Context, id uint64) error {
	return k.stakingKeeper.UnbondingCanComplete(ctx, id)
}

func (k Keeper) UnbondingTime(ctx sdk.Context) (time.Duration, error) {
	return k.stakingKeeper.UnbondingTime(ctx)
}
