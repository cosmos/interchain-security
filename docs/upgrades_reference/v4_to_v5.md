# Process


# Protos
Some proto files needed to be updated to reflect changes required for cosmos-sdk v50.

## Provider proto changes
Updated types and marked legacy proposal types as deprecated.

### proto/interchain_security/ccv/provider/v1/provider.proto
Added options `deprecated = true` and `(cosmos_proto.implements_interface) = "cosmos.gov.v1beta1.Content";` 
* `message ConsumerAdditionProposal`
* `message ConsumerRemovalProposal`
* `message ChangeRewardDenomsProposal`

### proto/interchain_security/ccv/provider/v1/tx.proto

Added rpc methods and message types to support v50 governance (`submit-proposal`)
* `rpc ConsumerAddition`
* `rpc ConsumerRemoval`
* `message MsgUpdateParams`
* `message MsgConsumerAddition`
* `message MsgConsumerRemoval`
* `message MsgChangeRewardDenoms`


Update existing messages with `option (cosmos.msg.v1.signer) = "signer"` so they are considered as Tx messages by v50.
* `message MsgAssignConsumerKey`



## Generating protos with updated dependencies:

```
# update Makefile containerProtoVersion to latest (v0.14.0)
cd proto
# update buf.yml
buf mod update
cd ..
make proto-gen
```

# Upgrading cosmos-sdk and ibc-go
Key dependencies:
* `cosmos-sdk@v0.50.4`
* `ibc-go/v8@v8.1.0`
* `ibc-go/modules/capability@v1.0.0`

```
go get github.com/cosmos/cosmos-sdk@v0.50.4
go get github.com/cosmos/ibc-go/v8@v8.1.0
```

Another new thing with `ibc-go/v8` is using the `x/capability` module that lives in `github.com/cosmos/ibc-go/modules/capability`.
* this module was added after all the file imports were changed for ibc-go (from v7 -> v8) to avoid weird import behaviour
	* one notable weridness is that the `go` tool tries to import `go: downloading github.com/cosmos/ibc-go v1.5.0`

### Search & replace
* github.com/cosmos/ibc-go/v7 -> github.com/cosmos/ibc-go/v8
* github.com/cosmos/cosmos-sdk/store -> cosmossdk.io/store
* github.com/cosmos/cosmos-sdk/x/feegrant -> cosmossdk.io/x/feegrant
* github.com/cosmos/cosmos-sdk/x/evidence -> cosmossdk.io/x/evidence
* github.com/cosmos/cosmos-sdk/x/upgrade -> cosmossdk.io/x/upgrade

* github.com/cometbft/cometbft/libs/log -> cosmossdk.io/log
* github.com/cosmos/cosmos-sdk/x/capability/keeper -> github.com/cosmos/ibc-go/modules/capability
* github.com/cosmos/cosmos-sdk/client/grpc/tmservice -> github.com/cosmos/cosmos-sdk/client/grpc/cmtservice

### Remove
cosmossdk.io/x/upgrade/client -> no longer exists and not needed


### Math search & replace
* use sdk.LegacyDec instead of sdk.Dec
	* also update all function defintions that are using them
* use math.NewInt instead of sdk.NewInt
	* also update all dunction definitions that are using them


### Expected Keepers




# Genesis
expedited_voting_period


# gov
We can keep legacy gov

# queries & Txs
AutoCLI added

Must annotate Txs with  option (cosmos.msg.v1.service) = true;

gogoproto stringer was removed

# IBC v8.0.0-beta.1
github.com/cosmos/interchain-security/v3/app/provider
app/provider/app.go:453:3: cannot use &app.IBCKeeper.PortKeeper (value of type **"github.com/cosmos/ibc-go/v8/modules/core/05-port/keeper".Keeper) as "github.com/cosmos/interchain-security/v3/x/ccv/types".PortKeeper value in argument to icsproviderkeeper.NewKeeper: **"github.com/cosmos/ibc-go/v8/modules/core/05-port/keeper".Keeper does not implement "github.com/cosmos/interchain-security/v3/x/ccv/types".PortKeeper (missing method BindPort)
app/provider/app.go:503:3: cannot use &app.IBCKeeper.PortKeeper (value of type **"github.com/cosmos/ibc-go/v8/modules/core/05-port/keeper".Keeper) as "github.com/cosmos/ibc-go/v8/modules/apps/transfer/types".PortKeeper value in argument to ibctransferkeeper.NewKeeper: **"github.com/cosmos/ibc-go/v8/modules/core/05-port/keeper".Keeper does not implement "github.com/cosmos/ibc-go/v8/modules/apps/transfer/types".PortKeeper (missing method BindPort)
make: *** [install] Error 1

```
// new interface

// PortKeeper defines the expected IBC port keeper
type PortKeeper interface {
	BindPort(ctx sdk.Context, portID string) error
}

```

Sometimes bugs exist so it's difficult to work with deps.


## Go get deps

```bash
# SDK
go get github.com/cosmos/cosmos-sdk@b7d9d4c8a9b6b8b61716d2023982d29bdc9839a6

# IBC-GO
go get github.com/cosmos/ibc-go@5ca37ef6e56a98683cf2b3b1570619dc9b322977

# x/capability moved to ibc-go/modules/capability
go get github.com/cosmos/ibc-go/modules/capability@v1.0.0-rc5
```

# Instructions
https://docs.cosmos.network/v0.50/migrations/upgrading

https://ibc.cosmos.network/main/migrations/v7-to-v8.html

# ICS MIGRATIONS
Migrate parameters to standalone if not there already.
Remove legacy props because those cannot be used
Migrate to depinject -> info is on v47
* https://docs.cosmos.network/v0.47/migrations/upgrading

Use sdk.LegacyDec instead of sdk.Dec
Use math.NewInt instead of sdk.NewInt
All other functions relating to sdk.Dec need to be migrated, so do all references to sdk.Int

# changes in function signature

func (k Keeper) GetValidator(ctx context.Context, addr sdk.ValAddress) (validator types.Validator, err error) {


# Staking
Interface changes in:
```
AfterValidatorCreated
AfterValidatorRemoved
BeforeDelegationCreated
BeforeDelegationSharesModified
AfterDelegationModified
BeforeValidatorSlashed
BeforeValidatorModified
AfterValidatorBonded
AfterValidatorBeginUnbonding
BeforeDelegationRemoved
```

`sdk.Context` replaced with `context.Context`
-> this poses an issue because the staking hooks call keeper methods with the wrong context
```
// This stores a record of each unbonding op from staking, allowing us to track which consumer chains have unbonded
func (h Hooks) AfterUnbondingInitiated(ctx context.Context, id uint64) error {
	var consumerChainIDS []string

    // errors since GetAllConsumerChains expects sdk.Context and not context.Context
	for _, chain := range h.k.GetAllConsumerChains(ctx) {
		consumerChainIDS = append(consumerChainIDS, chain.ChainId)
	}
```

Refactoring example from cosmos-sdk:
```
// iterate over delegator withdraw addrs
func (k Keeper) IterateDelegatorWithdrawAddrs(ctx context.Context, handler func(del, addr sdk.AccAddress) (stop bool)) {
	store := k.storeService.OpenKVStore(ctx)
	iter := storetypes.KVStorePrefixIterator(runtime.KVStoreAdapter(store), types.DelegatorWithdrawAddrPrefix)
	defer iter.Close()
	for ; iter.Valid(); iter.Next() {
		addr := sdk.AccAddress(iter.Value())
		del := types.GetDelegatorWithdrawInfoAddress(iter.Key())
		if handler(del, addr) {
			break
		}
	}
}
```

# Refactoring keepers

## Context
Instead of using `sdk.Context` we need to use `context.Context`.
After the refactor the store will be accessed via `k.storeService.OpenKVStore(ctx)` instead of `ctx.KVStore(k.storeKey)`.


## validator.GetConsAddr() no longer works
Cannot do `sdk.ConsAddress(validatorConsumerAddrs.ConsumerAddr).Equals(consensusAddr)` because `.Equals()` now takes a `sdk.Address` interface type.
Change to `sdk.ConsAddress(validatorConsumerAddrs.ConsumerAddr).Equals(sdk.ConsAddress(consensusAddr))`

// TODO: port v50
## Addr codecs
```
validatorAddressCodec addresscodec.Codec
consensusAddressCodec addresscodec.Codec
```


```
// Logger returns a module-specific logger.
func (k Keeper) Logger(ctx context.Context) log.Logger {
	sdkCtx := sdk.UnwrapSDKContext(ctx)
	return sdkCtx.Logger().With("module", "x/"+ibchost.ModuleName+"-"+types.ModuleName)
}
```

```
type Keeper struct {
	// the address capable of executing a MsgUpdateParams message. Typically, this
	// should be the x/gov module account.
	authority string

    // address codecs were added
    validatorAddressCodec addresscodec.Codec
	consensusAddressCodec addresscodec.Codec
}

## Gov authority 
// GetAuthority returns the module's authority.
func (k Keeper) GetAuthority() string {
	return k.authority
}

```
# Staking migration
-> all interface methods changed

## Setting hooks
In v50 hooks are setup in the `keeper.go`

```
// Hooks gets the hooks for staking *Keeper 
func (k *Keeper) Hooks() types.StakingHooks {
	if k.hooks == nil {
		// return a no-op implementation if no hooks are set
		return types.MultiStakingHooks{}
	}

	return k.hooks
}

// SetHooks sets the validator hooks.  In contrast to other receivers, this method must take a pointer due to nature
// of the hooks interface and SDK start up sequence.
func (k *Keeper) SetHooks(sh types.StakingHooks) {
	if k.hooks != nil {
		panic("cannot set validator hooks twice")
	}

	k.hooks = sh
}
```

## Proposals

sdk.Handler no longer exists and needs to be replaced
```
func NewHandler(k *keeper.Keeper) sdk.Handler {
	msgServer := keeper.NewMsgServerImpl(k)
    ...
}    
```

# Testing
NewInMemKeeperParams dont work any more
-> mocks need to be regenerated for the testing to work
-> I'm doing this incrementally


# ACTUAL NOTES
## provider keeper migration
* hooks
* key assignment
	-> issue with decoding, probably caused by me
* staking interface changes -> Validator, StakingKeeper
* UT updates


# changes to StakingKeeper interface mess up a bunch of things

```golang
func (k Keeper) GetLastValidatorPower(ctx sdk.Context, operator sdk.ValAddress) (power int64) {
	store := ctx.KVStore(k.storeKey)

	bz := store.Get(types.GetLastValidatorPowerKey(operator))
	if bz == nil {
		return 0
	}

	intV := gogotypes.Int64Value{}
	k.cdc.MustUnmarshal(bz, &intV)

	return intV.GetValue()
}


// NEW
// GetLastValidatorPower loads the last validator power.
// Returns zero if the operator was not a validator last block.
func (k Keeper) GetLastValidatorPower(ctx context.Context, operator sdk.ValAddress) (power int64, err error) {
	store := k.storeService.OpenKVStore(ctx)
	bz, err := store.Get(types.GetLastValidatorPowerKey(operator))
	if err != nil {
		return 0, err
	}

	if bz == nil {
		return 0, nil
	}

	intV := gogotypes.Int64Value{}
	err = k.cdc.Unmarshal(bz, &intV)
	if err != nil {
		return 0, err
	}

	return intV.GetValue(), nil
}

```

```golang
// AssignConsumerKey assigns the consumerKey to the validator with providerAddr
// on the consumer chain with ID chainID
func (k Keeper) AssignConsumerKey(
	ctx sdk.Context,
	chainID string,
	validator stakingtypes.Validator,
	consumerKey tmprotocrypto.PublicKey,
) error {
	consAddrTmp, err := ccvtypes.TMCryptoPublicKeyToConsAddr(consumerKey)
	if err != nil {
		return err
	}
	consumerAddr := types.NewConsumerConsAddress(consAddrTmp)

	consAddrTmp, err = validator.GetConsAddr()
	if err != nil {
		return err
	}
	providerAddr := types.NewProviderConsAddress(consAddrTmp)

	// NOTE: @MSalopek this changed to return errs from store
	if existingVal, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, consumerAddr.ToSdkConsAddr()); err == nil {
		// If there is a validator using the consumer key to validate on the provider
		// we prevent assigning the consumer key, unless the validator is assigning validator.
		// This ensures that a validator joining the active set who has not explicitly assigned
		// a consumer key, will be able to use their provider key as consumer key (as per default).
		if existingVal.OperatorAddress != validator.OperatorAddress {
			return errorsmod.Wrapf(
				types.ErrConsumerKeyInUse, "a different validator already uses the consumer key",
			)
		}
		_, found := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
		if !found {
			return errorsmod.Wrapf(
				types.ErrCannotAssignDefaultKeyAssignment,
				"a validator cannot assign the default key assignment unless its key on that consumer has already been assigned",
			)
		}
	}
```

```golang
var _ types.MsgServer = msgServer{}

// CreateValidator defines a method for creating a new validator
func (k msgServer) AssignConsumerKey(goCtx context.Context, msg *types.MsgAssignConsumerKey) (*types.MsgAssignConsumerKeyResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	// It is possible to assign keys for consumer chains that are not yet approved.
	// TODO: In future, a mechanism will be added to limit assigning keys to chains
	// which are approved or pending approval, only.
	// Note that current attack potential is restricted because validators must sign
	// the transaction, and the chainID size is limited.

	providerValidatorAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return nil, err
	}

	// validator must already be registered
	validator, err := k.stakingKeeper.GetValidator(ctx, providerValidatorAddr)
	if err != nil && err == stakingtypes.ErrNoValidatorFound {
		return nil, stakingtypes.ErrNoValidatorFound
	} else if err != nil {
		return nil, err
	}

	// parse consumer key as long as it's in the right format
	pkType, keyStr, err := types.ParseConsumerKeyFromJson(msg.ConsumerKey)
	if err != nil {
		return nil, err
	}
```



# evidencekeeper equiv handling is not privated
```go
type EvidenceKeeper interface {
	HandleEquivocationEvidence(ctx sdk.Context, evidence *evidencetypes.Equivocation)
}
```

```golang
// GetValidatorUpdates returns the ABCI validator power updates within the current block.
func (k Keeper) GetValidatorUpdates(ctx context.Context) ([]abci.ValidatorUpdate, error) {
	store := k.storeService.OpenKVStore(ctx)
	bz, err := store.Get(types.ValidatorUpdatesKey)
	if err != nil {
		return nil, err
	}

	var valUpdates types.ValidatorUpdates
	err = k.cdc.Unmarshal(bz, &valUpdates)
	if err != nil {
		return nil, err
	}

	return valUpdates.Updates, nil
}

// [old v47]
// GetValidatorUpdates returns the ABCI validator power updates within the current block.
func (k Keeper) GetValidatorUpdates(ctx sdk.Context) []abci.ValidatorUpdate {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ValidatorUpdatesKey)

	var valUpdates types.ValidatorUpdates
	k.cdc.MustUnmarshal(bz, &valUpdates)

	return valUpdates.Updates
}

```

```golang
// HandleSlashPacket potentially jails a misbehaving validator for a downtime infraction.
// This method should NEVER be called with a double-sign infraction.
func (k Keeper) HandleSlashPacket(ctx sdk.Context, chainID string, data ccv.SlashPacketData) {
	consumerConsAddr := providertypes.NewConsumerConsAddress(data.Validator.Address)
	// Obtain provider chain consensus address using the consumer chain consensus address
	providerConsAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerConsAddr)

	k.Logger(ctx).Debug("handling slash packet",
		"chainID", chainID,
		"consumer cons addr", consumerConsAddr.String(),
		"provider cons addr", providerConsAddr.String(),
		"vscID", data.ValsetUpdateId,
		"infractionType", data.Infraction,
	)

	// Obtain validator from staking keeper
	validator, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerConsAddr.ToSdkConsAddr())
	if err != nil && stakingtypes.ErrNoValidatorFound.Is(err) {
		k.Logger(ctx).Error("validator not found or is unbonded", "validator", providerConsAddr.String())
		return
	}
	// make sure the validator is not yet unbonded;
	// stakingKeeper.Slash() panics otherwise
	if !validator.IsUnbonded() {
		// if validator is not found or is unbonded, drop slash packet and log error.
		// Note that it is impossible for the validator to be not found or unbonded if both the provider
		// and the consumer are following the protocol. Thus if this branch is taken then one or both
		// chains is incorrect, but it is impossible to tell which.
		k.Logger(ctx).Error("validator not found or is unbonded", "validator", providerConsAddr.String())
		return
	}

	// tombstoned validators should not be slashed multiple times.
	if k.slashingKeeper.IsTombstoned(ctx, providerConsAddr.ToSdkConsAddr()) {
		// Log and drop packet if validator is tombstoned.
		k.Logger(ctx).Info(
			"slash packet dropped because validator is already tombstoned",
			"provider cons addr", providerConsAddr.String(),
		)
		return
	}

```
```go
func (k Keeper) HandleSlashPacket(ctx sdk.Context, chainID string, data ccv.SlashPacketData) {
	// jail validator
	if !validator.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerConsAddr.ToSdkConsAddr())
		k.Logger(ctx).Info("validator jailed", "provider cons addr", providerConsAddr.String())
		jailDuration, err := k.slashingKeeper.DowntimeJailDuration(ctx)
		// NOTE: @MSalopek -> seems a bit odd to just log maybe panic if downtime duration is not set?
		if err != nil {
			k.Logger(ctx).Error("failed to get jail duration", "err", err.Error())
			return
		}
		jailTime := ctx.BlockTime().Add(jailDuration)
		k.slashingKeeper.JailUntil(ctx, providerConsAddr.ToSdkConsAddr(), jailTime)
	}

```

# Changes for app.go
```go
package baseapp

import (
	"context"
	"io"
	"sync"

	abci "github.com/tendermint/tendermint/abci/types"

	store "github.com/cosmos/cosmos-sdk/store/types"
)

// ABCIListener interface used to hook into the ABCI message processing of the BaseApp.
// the error results are propagated to consensus state machine,
// if you don't want to affect consensus, handle the errors internally and always return `nil` in these APIs.
type ABCIListener interface {
	// ListenBeginBlock updates the streaming service with the latest BeginBlock messages
	ListenBeginBlock(ctx context.Context, req abci.RequestBeginBlock, res abci.ResponseBeginBlock) error
	// ListenEndBlock updates the steaming service with the latest EndBlock messages
	ListenEndBlock(ctx context.Context, req abci.RequestEndBlock, res abci.ResponseEndBlock) error
	// ListenDeliverTx updates the steaming service with the latest DeliverTx messages
	ListenDeliverTx(ctx context.Context, req abci.RequestDeliverTx, res abci.ResponseDeliverTx) error
	// ListenCommit updates the steaming service with the latest Commit event
	ListenCommit(ctx context.Context, res abci.ResponseCommit) error
}

// StreamingService interface for registering WriteListeners with the BaseApp and updating the service with the ABCI messages using the hooks
type StreamingService interface {
	// Stream is the streaming service loop, awaits kv pairs and writes them to some destination stream or file
	Stream(wg *sync.WaitGroup) error
	// Listeners returns the streaming service's listeners for the BaseApp to register
	Listeners() map[store.StoreKey][]store.WriteListener
	// ABCIListener interface for hooking into the ABCI messages from inside the BaseApp
	ABCIListener
	// Closer interface
	io.Closer
}

```

```golang
// Obtains the effective validator power relevant to a validator consensus address.
func (k Keeper) GetEffectiveValPower(ctx sdktypes.Context,
	valConsAddr providertypes.ProviderConsAddress,
) math.Int {
	// Obtain staking module val object from the provider's consensus address.
	// Note: if validator is not found or unbonded, this will be handled appropriately in HandleSlashPacket
	val, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, valConsAddr.ToSdkConsAddr())

	if err != nil || val.IsJailed() {
		// If validator is not found, or found but jailed, it's power is 0. This path is explicitly defined since the
		// staking keeper's LastValidatorPower values are not updated till the staking keeper's endblocker.
		return math.ZeroInt()
	} else {
		// NOTE: @MSalopek -> Is this is an error?
		// Otherwise, return the staking keeper's LastValidatorPower value.
		valAddrBech32, err := sdk.ValAddressFromHex(val.GetOperator())
		if err != nil {
			return math.ZeroInt()
		}
		return math.NewInt(k.stakingKeeper.GetLastValidatorPower(ctx, valAddrBech32))
	}
}

```

# consumer
```
// ChangeoverToConsumer includes the logic that needs to execute during the process of a
// standalone to consumer changeover, where the previously standalone chain has
// just been upgraded to include the consumer ccv module, but the provider valset is not
// yet responsible for POS/block production. This method constructs validator updates
// that will be given to tendermint, which allows the consumer chain to
// start using the provider valset, while the standalone valset is given zero voting power where appropriate.
func (k Keeper) ChangeoverToConsumer(ctx sdk.Context) (initialValUpdates []abci.ValidatorUpdate) {
	// populate cross chain validators states with initial valset
	initialValUpdates = k.GetInitialValSet(ctx)
	k.ApplyCCValidatorChanges(ctx, initialValUpdates)

	// Add validator updates to initialValUpdates, such that the "old" validators returned from standalone staking module
	// are given zero power, and the provider validators are given their full power.
	initialUpdatesFlag := make(map[string]bool)
	for _, val := range initialValUpdates {
		initialUpdatesFlag[val.PubKey.String()] = true
	}

	// NOTE: panics now!
	standaloneValset, err := k.GetLastStandaloneValidators(ctx)
	if err != nil {
		panic(err)
	}
	for _, val := range k.GetLastStandaloneValidators(ctx) {
		zeroPowerUpdate := val.ABCIValidatorUpdateZero()
		if !initialUpdatesFlag[zeroPowerUpdate.PubKey.String()] {
			initialValUpdates = append(initialValUpdates, zeroPowerUpdate)
		}
	}

	// Note: this method should only be executed once as a part of the changeover process.
	// Therefore we set the PreCCV state to false so the endblocker caller doesn't call this method again.
	k.DeletePreCCV(ctx)

	k.Logger(ctx).Info("ICS changeover complete - you are now a consumer chain!")
	return initialValUpdates
}

```

This returns error from now on
```go
// IsJailed returns the outstanding slashing flag for the given validator adddress
func (k Keeper) IsValidatorJailed(ctx sdk.Context, addr sdk.ConsAddress) (bool, error) {
	// if the changeover is not complete for prev standalone chain,
	// return the standalone staking keeper's jailed status
	if k.IsPrevStandaloneChain(ctx) && !k.ChangeoverIsComplete(ctx) {
		return k.standaloneStakingKeeper.IsValidatorJailed(ctx, addr)
	}
	// Otherwise, return the ccv consumer keeper's notion of a validator being jailed
	return k.OutstandingDowntime(ctx, addr), nil
}

```



# consumer Keeper overrides
Add missing:

## keeper

############################################
## REMEMBER TO SWTICTH TO USING STORESERVICE
############################################

Usage of `sdk.Context` must be replaced with `context.Context` for all Staking methods because the Staking interface changed.

How I figured this out and when:
- when I re-wired app.go `app.ConsumerKeeper` was raising errors because of wrong interface method signatures.

```
GetParams -> now returns err

Jail -> now returns err
Unjail -> now returns err
IsValidatorJailed -> matches SDK.Staking, ctx gets unwrapped by sdkCtx := sdk.UnwrapSDKContext(ctx)


Delegation
MaxValidators
UnbondingTime
GetHistoricalInfo -> changes signature to return err -> matches SDK.Staking
TrackHistoricalInfo -> changes signature to return err -> matches SDK.Staking
DeleteHistoricalInfo -> changes signature to return err -> matches SDK.Staking


Validator 
GetAllValidators -> changes signature to return err -> matches SDK.Staking 
IterateValidators -> changes signature to use context.Context -> matches SDK.Staking 

Slash -> changes signature to use context.Context -> matches SDK.Staking 

SlashWithInfractionReason -> changes signature to use context.Context -> matches SDK.Staking -> must use sdkCtx := sdk.UnwrapSDKContext(ctx)

GetUnbondingPeriod -> changes signature to use context.Context -> matches SDK.Staking -> must use sdkCtx := sdk.UnwrapSDKContext(ctx); returns err

ApplyAndReturnValidatorSetUpdate -> changes signature to use context.Context -> matches SDK.Staking -> must use sdkCtx := sdk.UnwrapSDKContext(ctx); returns err

# hooks
# type ConsumerHooks interface
AfterValidatorBonded -> changes signature to use context.Context
```


```
// ValidatorAddressCodec returns the app validator address codec.
func (k Keeper) ValidatorAddressCodec() addresscodec.Codec {
	return k.validatorAddressCodec
}

// ConsensusAddressCodec returns the app consensus address codec.
func (k Keeper) ConsensusAddressCodec() addresscodec.Codec {
	return k.consensusAddressCodec
}

```

# Democracy
-> staking -> minor, possibly not required?
-> distribution -> didn't touch
-> gov -> there's not iterator so we need to use collections
