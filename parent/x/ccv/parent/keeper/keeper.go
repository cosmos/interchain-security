package keeper

import (
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	capabilitykeeper "github.com/cosmos/cosmos-sdk/x/capability/keeper"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/modules/core/24-host"
	ibcexported "github.com/cosmos/ibc-go/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/parent/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/tendermint/tendermint/libs/log"
)

// Keeper defines the Cross-Chain Validation Parent Keeper
type Keeper struct {
	storeKey         sdk.StoreKey
	cdc              codec.BinaryCodec
	scopedKeeper     capabilitykeeper.ScopedKeeper
	channelKeeper    ccv.ChannelKeeper
	portKeeper       ccv.PortKeeper
	connectionKeeper ccv.ConnectionKeeper
	clientKeeper     ccv.ClientKeeper
	registryKeeper   ccv.RegistryKeeper
}

// NewKeeper creates a new parent Keeper instance
func NewKeeper(
	cdc codec.BinaryCodec, key sdk.StoreKey, scopedKeeper capabilitykeeper.ScopedKeeper,
	channelKeeper ccv.ChannelKeeper, portKeeper ccv.PortKeeper,
	connectionKeeper ccv.ConnectionKeeper, clientKeeper ccv.ClientKeeper,
	registryKeeper ccv.RegistryKeeper,
) Keeper {
	return Keeper{
		cdc:              cdc,
		storeKey:         key,
		scopedKeeper:     scopedKeeper,
		channelKeeper:    channelKeeper,
		portKeeper:       portKeeper,
		connectionKeeper: connectionKeeper,
		clientKeeper:     clientKeeper,
		registryKeeper:   registryKeeper,
	}
}

// Logger returns a module-specific logger.
func (k Keeper) Logger(ctx sdk.Context) log.Logger {
	return ctx.Logger().With("module", "x/"+host.ModuleName+"-"+types.ModuleName)
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

// SetChainToChannel sets the mapping from a baby chainID to the CCV channel ID for that baby chain.
func (k Keeper) SetChainToChannel(ctx sdk.Context, chainID, channelID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ChainToChannelKey(chainID), []byte(channelID))
}

// GetChainToChannel gets the CCV channelID for the given baby chainID
func (k Keeper) GetChainToChannel(ctx sdk.Context, chainID string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ChainToChannelKey(chainID))
	if bz == nil {
		return "", false
	}
	return string(bz), true
}

// IterateBabyChains iterates over all of the baby chains that the parent module controls.
// It calls the provided callback function which takes in a chainID and channelID and returns
// a stop boolean which will stop the iteration.
func (k Keeper) IterateBabyChains(ctx sdk.Context, cb func(ctx sdk.Context, chainID string) (stop bool)) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte(types.ChainToChannelKeyPrefix+"/"))
	defer iterator.Close()

	if !iterator.Valid() {
		return
	}

	for ; iterator.Valid(); iterator.Next() {
		chainID := string(iterator.Key())

		stop := cb(ctx, chainID)
		if stop {
			return
		}
	}
}

// SetChannelToChain sets the mapping from the CCV channel ID to the baby chainID.
func (k Keeper) SetChannelToChain(ctx sdk.Context, channelID, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ChannelToChainKey(channelID), []byte(chainID))
}

// GetChannelToChain gets the baby chainID for a given CCV channelID
func (k Keeper) GetChannelToChain(ctx sdk.Context, channelID string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ChannelToChainKey(channelID))
	if bz == nil {
		return "", false
	}
	return string(bz), true
}

// IterateChannelToChain iterates over the channel to chain mappings and calls the provided callback until the iteration ends
// or the callback returns stop=true
func (k Keeper) IterateChannelToChain(ctx sdk.Context, cb func(ctx sdk.Context, channelID, chainID string) (stop bool)) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte(types.ChannelToChainKeyPrefix+"/"))
	defer iterator.Close()

	if !iterator.Valid() {
		return
	}

	for ; iterator.Valid(); iterator.Next() {
		channelID := string(iterator.Key())
		chainID := string(iterator.Value())

		if cb(ctx, channelID, chainID) {
			break
		}
	}
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

// VerifyChildChain verifies that the chain trying to connect on the channel handshake
// is the expected baby chain.
func (k Keeper) VerifyChildChain(ctx sdk.Context, channelID string) error {
	// Verify CCV channel is in Initialized state
	status := k.GetChannelStatus(ctx, channelID)
	if status != ccv.INITIALIZING {
		return sdkerrors.Wrap(ccv.ErrInvalidStatus, "CCV channel status must be in Initializing state")
	}
	clientID, tmClient, err := k.getUnderlyingClient(ctx, channelID)
	if err != nil {
		return err
	}
	ccvClientId := k.GetChildClient(ctx, tmClient.ChainId)
	if ccvClientId != clientID {
		return sdkerrors.Wrapf(ccv.ErrInvalidChildClient, "CCV channel must be built on top of CCV client. expected %s, got %s", ccvClientId, clientID)
	}

	// Verify that there isn't already a CCV channel for the child chain
	if prevChannel, ok := k.GetChainToChannel(ctx, tmClient.ChainId); ok {
		return sdkerrors.Wrapf(ccv.ErrDuplicateChannel, "CCV channel with ID: %s already created for child chain %s", prevChannel, tmClient.ChainId)
	}
	return nil
}

// SetChildChain ensures that the child chain has not already been set by a different channel, and then sets the child chain mappings in keeper,
// and set the channel status to validating.
// If there is already a ccv channel between the parent and child chain then close the channel, so that another channel can be made.
func (k Keeper) SetChildChain(ctx sdk.Context, channelID string) error {
	chainID, tmClient, err := k.getUnderlyingClient(ctx, channelID)
	if err != nil {
		return err
	}
	// Verify that there isn't already a CCV channel for the child chain
	// If there is, then close the channel.
	if prevChannel, ok := k.GetChannelToChain(ctx, chainID); ok {
		k.SetChannelStatus(ctx, channelID, ccv.INVALID)
		k.chanCloseInit(ctx, channelID)
		return sdkerrors.Wrapf(ccv.ErrDuplicateChannel, "CCV channel with ID: %s already created for child chain %s", prevChannel, chainID)
	}
	// set channel mappings
	k.SetChainToChannel(ctx, tmClient.ChainId, channelID)
	k.SetChannelToChain(ctx, channelID, tmClient.ChainId)
	// Set CCV channel status to Validating
	k.SetChannelStatus(ctx, channelID, ccv.VALIDATING)
	return nil
}

func (k Keeper) getUnderlyingClient(ctx sdk.Context, channelID string) (string, *ibctmtypes.ClientState, error) {
	// Retrieve the underlying client state.
	channel, ok := k.channelKeeper.GetChannel(ctx, types.PortID, channelID)
	if !ok {
		return "", nil, sdkerrors.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for channel ID: %s", channelID)
	}
	if len(channel.ConnectionHops) != 1 {
		return "", nil, sdkerrors.Wrap(channeltypes.ErrTooManyConnectionHops, "must have direct connection to baby chain")
	}
	connectionID := channel.ConnectionHops[0]
	conn, ok := k.connectionKeeper.GetConnection(ctx, connectionID)
	if !ok {
		return "", nil, sdkerrors.Wrapf(conntypes.ErrConnectionNotFound, "connection not found for connection ID: %s", connectionID)
	}
	client, ok := k.clientKeeper.GetClientState(ctx, conn.ClientId)
	if !ok {
		return "", nil, sdkerrors.Wrapf(clienttypes.ErrClientNotFound, "client not found for client ID: %s", conn.ClientId)
	}
	tmClient, ok := client.(*ibctmtypes.ClientState)
	if !ok {
		return "", nil, sdkerrors.Wrapf(clienttypes.ErrInvalidClientType, "invalid client type. expected %s, got %s", ibcexported.Tendermint, client.ClientType())
	}
	return conn.ClientId, tmClient, nil
}

// chanCloseInit defines a wrapper function for the channel Keeper's function
func (k Keeper) chanCloseInit(ctx sdk.Context, channelID string) error {
	capName := host.ChannelCapabilityPath(types.PortID, channelID)
	chanCap, ok := k.scopedKeeper.GetCapability(ctx, capName)
	if !ok {
		return sdkerrors.Wrapf(channeltypes.ErrChannelCapabilityNotFound, "could not retrieve channel capability at: %s", capName)
	}
	return k.channelKeeper.ChanCloseInit(ctx, types.PortID, channelID, chanCap)
}
