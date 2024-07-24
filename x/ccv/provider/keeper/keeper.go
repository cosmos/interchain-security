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

// SetProposedConsumerChain stores a consumer chainId corresponding to a submitted consumer addition proposal
// This consumer chainId is deleted once the voting period for the proposal ends.
func (k Keeper) SetProposedConsumerChain(ctx sdk.Context, chainID string, proposalID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ProposedConsumerChainKey(proposalID), []byte(chainID))
}

// GetProposedConsumerChain returns the proposed chainID for the given consumerAddition proposal ID.
// This method is only used for testing.
func (k Keeper) GetProposedConsumerChain(ctx sdk.Context, proposalID uint64) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	consumerChain := store.Get(types.ProposedConsumerChainKey(proposalID))
	if consumerChain != nil {
		return string(consumerChain), true
	}
	return "", false
}

// DeleteProposedConsumerChainInStore deletes the consumer chainID from store
// which is in gov consumerAddition proposal
func (k Keeper) DeleteProposedConsumerChainInStore(ctx sdk.Context, proposalID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ProposedConsumerChainKey(proposalID))
}

// GetAllProposedConsumerChainIDs returns the proposed chainID of all gov consumerAddition proposals that are still in the voting period.
func (k Keeper) GetAllProposedConsumerChainIDs(ctx sdk.Context) []types.ProposedChain {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ProposedConsumerChainKeyPrefix())
	defer iterator.Close()

	proposedChains := []types.ProposedChain{}
	for ; iterator.Valid(); iterator.Next() {
		proposalID, err := types.ParseProposedConsumerChainKey(iterator.Key())
		if err != nil {
			panic(fmt.Errorf("proposed chains cannot be parsed: %w", err))
		}

		proposedChains = append(proposedChains, types.ProposedChain{
			ChainID:    string(iterator.Value()),
			ProposalID: proposalID,
		})

	}

	return proposedChains
}

// GetAllPendingConsumerChainIDs gets pending consumer chains have not reach spawn time
func (k Keeper) GetAllPendingConsumerChainIDs(ctx sdk.Context) []string {
	chainIDs := []string{}
	props := k.GetAllPendingConsumerAdditionProps(ctx)
	for _, prop := range props {
		chainIDs = append(chainIDs, prop.ChainId)
	}

	return chainIDs
}

// GetAllRegisteredConsumerChainIDs gets all of the consumer chain IDs, for which the provider module
// created IBC clients. Consumer chains with created clients are also referred to as registered.
//
// Note that the registered consumer chains are stored under keys with the following format:
// ChainToClientKeyPrefix | chainID
// Thus, the returned array is in ascending order of chainIDs.
func (k Keeper) GetAllRegisteredConsumerChainIDs(ctx sdk.Context) []string {
	chainIDs := []string{}

	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ChainToClientKeyPrefix())
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// remove 1 byte prefix from key to retrieve chainID
		chainID := string(iterator.Key()[1:])
		chainIDs = append(chainIDs, chainID)
	}

	return chainIDs
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
// ChannelToChainKeyPrefix | channelID
// Thus, the returned array is in ascending order of channelIDs.
func (k Keeper) GetAllChannelToChains(ctx sdk.Context) (channels []types.ChannelToChain) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ChannelToChainKeyPrefix())
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

func (k Keeper) SetConsumerGenesis(ctx sdk.Context, chainID string, gen ccv.ConsumerGenesisState) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := gen.Marshal()
	if err != nil {
		return err
	}
	store.Set(types.ConsumerGenesisKey(chainID), bz)

	return nil
}

func (k Keeper) GetConsumerGenesis(ctx sdk.Context, chainID string) (ccv.ConsumerGenesisState, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerGenesisKey(chainID))
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
		return errorsmod.Wrapf(types.ErrInvalidConsumerClient, "CCV channel must be built on top of CCV client. expected %s, got %s", ccvClientId, clientID)
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
	var packets types.ValidatorSetChangePackets

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
	packets := types.ValidatorSetChangePackets{List: pds}
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

func (k Keeper) GetAllRegisteredAndProposedChainIDs(ctx sdk.Context) []string {
	allConsumerChains := []string{}
	allConsumerChains = append(allConsumerChains, k.GetAllRegisteredConsumerChainIDs(ctx)...)
	proposedChains := k.GetAllProposedConsumerChainIDs(ctx)
	for _, proposedChain := range proposedChains {
		allConsumerChains = append(allConsumerChains, proposedChain.ChainID)
	}
	pendingChainIDs := k.GetAllPendingConsumerChainIDs(ctx)
	allConsumerChains = append(allConsumerChains, pendingChainIDs...)

	return allConsumerChains
}

// SetTopN stores the N value associated to chain with `chainID`
func (k Keeper) SetTopN(
	ctx sdk.Context,
	chainID string,
	N uint32,
) {
	store := ctx.KVStore(k.storeKey)

	buf := make([]byte, 4)
	binary.BigEndian.PutUint32(buf, N)

	store.Set(types.TopNKey(chainID), buf)
}

// DeleteTopN removes the N value associated to chain with `chainID`
func (k Keeper) DeleteTopN(
	ctx sdk.Context,
	chainID string,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.TopNKey(chainID))
}

// GetTopN returns (N, true) if chain `chainID` has a top N associated, and (0, false) otherwise.
func (k Keeper) GetTopN(
	ctx sdk.Context,
	chainID string,
) (uint32, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.TopNKey(chainID))
	if buf == nil {
		return 0, false
	}
	return binary.BigEndian.Uint32(buf), true
}

// IsTopN returns true if chain with `chainID` is a Top-N chain (i.e., enforces at least one validator to validate chain `chainID`)
func (k Keeper) IsTopN(ctx sdk.Context, chainID string) bool {
	topN, found := k.GetTopN(ctx, chainID)
	return found && topN > 0
}

// IsOptIn returns true if chain with `chainID` is an Opt-In chain (i.e., no validator is forced to validate chain `chainID`)
func (k Keeper) IsOptIn(ctx sdk.Context, chainID string) bool {
	topN, found := k.GetTopN(ctx, chainID)
	return !found || topN == 0
}

func (k Keeper) SetOptedIn(
	ctx sdk.Context,
	chainID string,
	providerConsAddress types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.OptedInKey(chainID, providerConsAddress), []byte{})
}

func (k Keeper) DeleteOptedIn(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.OptedInKey(chainID, providerAddr))
}

func (k Keeper) IsOptedIn(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Get(types.OptedInKey(chainID, providerAddr)) != nil
}

// GetAllOptedIn returns all the opted-in validators on chain `chainID`
func (k Keeper) GetAllOptedIn(
	ctx sdk.Context,
	chainID string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.OptedInKeyPrefix(), chainID)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// DeleteAllOptedIn deletes all the opted-in validators for chain with `chainID`
func (k Keeper) DeleteAllOptedIn(
	ctx sdk.Context,
	chainID string,
) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.OptedInKeyPrefix(), chainID)
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
	chainID string,
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

	store.Set(types.ConsumerCommissionRateKey(chainID, providerAddr), bz)
	return nil
}

// GetConsumerCommissionRate returns the per-consumer commission rate set
// for the given validator address
func (k Keeper) GetConsumerCommissionRate(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) (math.LegacyDec, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerCommissionRateKey(chainID, providerAddr))
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
// that set a commission rate for the given chain ID
func (k Keeper) GetAllCommissionRateValidators(
	ctx sdk.Context,
	chainID string,
) (addresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.ConsumerCommissionRateKeyPrefix(), chainID)
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
	chainID string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerCommissionRateKey(chainID, providerAddr))
}

// SetValidatorsPowerCap sets the power-cap value `p` associated to chain with `chainID`
func (k Keeper) SetValidatorsPowerCap(
	ctx sdk.Context,
	chainID string,
	p uint32,
) {
	store := ctx.KVStore(k.storeKey)

	buf := make([]byte, 4)
	binary.BigEndian.PutUint32(buf, p)

	store.Set(types.ValidatorsPowerCapKey(chainID), buf)
}

// DeleteValidatorsPowerCap removes the power-cap value associated to chain with `chainID`
func (k Keeper) DeleteValidatorsPowerCap(
	ctx sdk.Context,
	chainID string,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValidatorsPowerCapKey(chainID))
}

// GetValidatorsPowerCap returns `(p, true)` if chain `chainID` has power cap `p` associated with it, and (0, false) otherwise
func (k Keeper) GetValidatorsPowerCap(
	ctx sdk.Context,
	chainID string,
) (uint32, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ValidatorsPowerCapKey(chainID))
	if buf == nil {
		return 0, false
	}
	return binary.BigEndian.Uint32(buf), true
}

// SetValidatorSetCap stores the validator-set cap value `c` associated to chain with `chainID`
func (k Keeper) SetValidatorSetCap(
	ctx sdk.Context,
	chainID string,
	c uint32,
) {
	store := ctx.KVStore(k.storeKey)

	buf := make([]byte, 4)
	binary.BigEndian.PutUint32(buf, c)

	store.Set(types.ValidatorSetCapKey(chainID), buf)
}

// DeleteValidatorSetCap removes the validator-set cap value associated to chain with `chainID`
func (k Keeper) DeleteValidatorSetCap(
	ctx sdk.Context,
	chainID string,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValidatorSetCapKey(chainID))
}

// GetValidatorSetCap returns `(c, true)` if chain `chainID` has validator-set cap `c` associated with it, and (0, false) otherwise
func (k Keeper) GetValidatorSetCap(
	ctx sdk.Context,
	chainID string,
) (uint32, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ValidatorSetCapKey(chainID))
	if buf == nil {
		return 0, false
	}
	return binary.BigEndian.Uint32(buf), true
}

// SetAllowlist allowlists validator with `providerAddr` address on chain `chainID`
func (k Keeper) SetAllowlist(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.AllowlistKey(chainID, providerAddr), []byte{})
}

// GetAllowList returns all allowlisted validators
func (k Keeper) GetAllowList(
	ctx sdk.Context,
	chainID string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.AllowlistKeyPrefix(), chainID)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// IsAllowlisted returns `true` if validator with `providerAddr` has been allowlisted on chain `chainID`
func (k Keeper) IsAllowlisted(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.AllowlistKey(chainID, providerAddr))
	return bz != nil
}

// DeleteAllowlist deletes all allowlisted validators
func (k Keeper) DeleteAllowlist(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.AllowlistKeyPrefix(), chainID))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// IsAllowlistEmpty returns `true` if no validator is allowlisted on chain `chainID`
func (k Keeper) IsAllowlistEmpty(ctx sdk.Context, chainID string) bool {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.AllowlistKeyPrefix(), chainID))
	defer iterator.Close()

	return !iterator.Valid()
}

// SetDenylist denylists validator with `providerAddr` address on chain `chainID`
func (k Keeper) SetDenylist(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.DenylistKey(chainID, providerAddr), []byte{})
}

// GetDenyList returns all denylisted validators
func (k Keeper) GetDenyList(
	ctx sdk.Context,
	chainID string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.DenylistKeyPrefix(), chainID)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// IsDenylisted returns `true` if validator with `providerAddr` has been denylisted on chain `chainID`
func (k Keeper) IsDenylisted(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.DenylistKey(chainID, providerAddr))
	return bz != nil
}

// DeleteDenylist deletes all denylisted validators
func (k Keeper) DeleteDenylist(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.DenylistKeyPrefix(), chainID))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// IsDenylistEmpty returns `true` if no validator is denylisted on chain `chainID`
func (k Keeper) IsDenylistEmpty(ctx sdk.Context, chainID string) bool {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ChainIdWithLenKey(types.DenylistKeyPrefix(), chainID))
	defer iterator.Close()

	return !iterator.Valid()
}

// SetMinimumPowerInTopN sets the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) SetMinimumPowerInTopN(
	ctx sdk.Context,
	chainID string,
	power int64,
) {
	store := ctx.KVStore(k.storeKey)

	buf := make([]byte, 8)
	binary.BigEndian.PutUint64(buf, uint64(power))

	store.Set(types.MinimumPowerInTopNKey(chainID), buf)
}

// GetMinimumPowerInTopN returns the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) GetMinimumPowerInTopN(
	ctx sdk.Context,
	chainID string,
) (int64, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.MinimumPowerInTopNKey(chainID))
	if buf == nil {
		return 0, false
	}
	return int64(binary.BigEndian.Uint64(buf)), true
}

// DeleteMinimumPowerInTopN removes the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) DeleteMinimumPowerInTopN(
	ctx sdk.Context,
	chainID string,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.MinimumPowerInTopNKey(chainID))
}

func (k Keeper) UnbondingCanComplete(ctx sdk.Context, id uint64) error {
	return k.stakingKeeper.UnbondingCanComplete(ctx, id)
}

func (k Keeper) UnbondingTime(ctx sdk.Context) (time.Duration, error) {
	return k.stakingKeeper.UnbondingTime(ctx)
}

func (k Keeper) GetBinaryCodec() codec.BinaryCodec {
	return k.cdc
}
