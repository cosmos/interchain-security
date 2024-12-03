---
sidebar_position: 4
---

# x/ccv/democracy

The democracy modules comprise `x/ccv/democracy/staking` and `x/ccv/democracy/distribution` with overrides and extensions required for normal operation when participating in ICS.

The modules are plug-and-play and only require small wiring changes to be enabled.

For a full integration check the `consumer-democracy` [example app](https://github.com/cosmos/interchain-security/blob/main/app/consumer-democracy/app.go).

## Staking

The `x/ccv/democracy/staking` module allows the cosmos-sdk `x/staking` module to be used alongside the interchain security `consumer` module.

The module uses overrides that allow the full `x/staking` functionality with one notable difference - the staking module will no longer be used to provide the validator set to the consensus engine.

### Implications for consumer chains

The `x/ccv/democracy/staking` allows consumer chains to **_separate governance from block production_**.
The validator set coming from the provider chain does not need to participate in governance - they only provide infrastructure (create blocks and maintain consensus).

#### Governators (aka. Governors)

Validators registered with the `x/ccv/democracy/staking` module become __Governators__.
Unlike validators, governators are not required to run any chain infrastructure since they are not signing any blocks.
However, governators retain a subset of the validator properties:

- new governators can be created (via `MsgCreateValidator`)
- governators can accept delegations
- governators can vote on governance proposals (with their self stake and delegations)
- governators earn block rewards -- the block rewards kept on the consumer (see the [ConsumerRedistributionFraction param](./03-consumer.md#consumerredistributionfraction)) are distributed to all governators and their delegators.

With these changes, governators can become community advocates that can specialize in chain governance and they get rewarded for their participation the same way the validators do.
Additionally, governators can choose to provide additional infrastructure such as RPC/API access points, archive nodes, indexers and similar software.

#### Tokenomics

The consumer chain's token will remain a governance token. The token's parameters (inflation, max supply, burn rate) are completely under the control of the consumer chain.

### Integration

The `x/ccv/democracy/staking` module provides these `x/staking` overrides:

```golang

// InitGenesis delegates the InitGenesis call to the underlying x/staking module,
// however, it returns no validator updates as validators are tracked via the
// consumer chain's x/cvv/consumer module and so this module is not responsible for returning the initial validator set.
func (am AppModule) InitGenesis(ctx sdk.Context, cdc codec.JSONCodec, data json.RawMessage) []abci.ValidatorUpdate {
    var genesisState types.GenesisState

    cdc.MustUnmarshalJSON(data, &genesisState)
    _ = am.keeper.InitGenesis(ctx, &genesisState)  // run staking InitGenesis

    return []abci.ValidatorUpdate{}  // do not return validator updates
}

// EndBlock delegates the EndBlock call to the underlying x/staking module.
// However, no validator updates are returned as validators are tracked via the
// consumer chain's x/cvv/consumer module.
func (am AppModule) EndBlock(ctx sdk.Context, _ abci.RequestEndBlock) []abci.ValidatorUpdate {
    _ = am.keeper.BlockValidatorUpdates(ctx)  // perform staking BlockValidatorUpdates
    return []abci.ValidatorUpdate{}  // do not return validator updates
}
```

To integrate the `democracy/staking` follow this guide:

#### 1. confirm that no modules are returning validator updates

:::warning
Only the `x/ccv/consumer` module should be returning validator updates.
:::

If some of your modules are returning validator updates please disable them while maintaining your business logic:

```diff
func (am AppModule) InitGenesis(ctx sdk.Context, cdc codec.JSONCodec, data json.RawMessage) []abci.ValidatorUpdate {
    var genesisState types.GenesisState

    cdc.MustUnmarshalJSON(data, &genesisState)
-	return am.keeper.InitGenesis(ctx, &genesisState)
+ 	_ = am.keeper.InitGenesis(ctx, &genesisState)  // run InitGenesis but drop the result
+	return []abci.ValidatorUpdate{}  // return empty validator updates
}


func (am AppModule) EndBlock(ctx sdk.Context, _ abci.RequestEndBlock) []abci.ValidatorUpdate {
-	return am.keeper.BlockValidatorUpdates(ctx)
+ 	_ = am.keeper.BlockValidatorUpdates(ctx)  // perform staking BlockValidatorUpdates
+	return []abci.ValidatorUpdate{}  // return empty validator updates
}
```

#### 2. wire the module in app.go

You **do not need to remove** the cosmos-sdk `StakingKeeper` from your wiring.

```diff
import (
    ...
+   ccvstaking "github.com/cosmos/interchain-security/v4/x/ccv/democracy/staking"
)

var (
    // replace the staking.AppModuleBasic
    ModuleBasics = module.NewBasicManager(
        auth.AppModuleBasic{},
        genutil.NewAppModuleBasic(genutiltypes.DefaultMessageValidator),
        bank.AppModuleBasic{},
        capability.AppModuleBasic{},
-		sdkstaking.AppModuleBasic{},
+		ccvstaking.AppModuleBasic{},  // replace sdkstaking
        ...
    )
)


func NewApp(...) {
    ...

    // use sdk StakingKeepeer
    app.StakingKeeper = stakingkeeper.NewKeeper(
        appCodec,
        keys[stakingtypes.StoreKey],
        app.AccountKeeper,
        app.BankKeeper,
        authtypes.NewModuleAddress(govtypes.ModuleName).String(),
    )

    app.MintKeeper = mintkeeper.NewKeeper(
        appCodec,
        keys[minttypes.StoreKey],
        app.StakingKeeper,
        app.AccountKeeper,
        app.BankKeeper,
        authtypes.FeeCollectorName,
        authtypes.NewModuleAddress(govtypes.ModuleName).String(),
    )

    // no changes required for the distribution keeper
    app.DistrKeeper = distrkeeper.NewKeeper(
        appCodec,
        keys[distrtypes.StoreKey],
        app.AccountKeeper,
        app.BankKeeper,
        app.StakingKeeper,  // keep StakingKeeper!
        authtypes.FeeCollectorName,
        authtypes.NewModuleAddress(govtypes.ModuleName).String(),
    )

+   // pre-initialize ConsumerKeeper to satsfy ibckeeper.NewKeeper
+	app.ConsumerKeeper = consumerkeeper.NewNonZeroKeeper(
+		appCodec,
+		keys[consumertypes.StoreKey],
+		app.GetSubspace(consumertypes.ModuleName),
+	)
+
+	app.IBCKeeper = ibckeeper.NewKeeper(
+		appCodec,
+		keys[ibchost.StoreKey],
+		app.GetSubspace(ibchost.ModuleName),
+		&app.ConsumerKeeper,
+		app.UpgradeKeeper,
+		scopedIBCKeeper,
+	)
+
+	// Create CCV consumer and modules
+	app.ConsumerKeeper = consumerkeeper.NewKeeper(
+		appCodec,
+		keys[consumertypes.StoreKey],
+		app.GetSubspace(consumertypes.ModuleName),
+		scopedIBCConsumerKeeper,
+		app.IBCKeeper.ChannelKeeper,
+		&app.IBCKeeper.PortKeeper,
+		app.IBCKeeper.ConnectionKeeper,
+		app.IBCKeeper.ClientKeeper,
+		app.SlashingKeeper,
+		app.BankKeeper,
+		app.AccountKeeper,
+		&app.TransferKeeper,
+		app.IBCKeeper,
+		authtypes.FeeCollectorName,
+	)
+
+	// Setting the standalone staking keeper is only needed for standalone to consumer changeover chains
+  	// New chains using the democracy/staking do not need to set this
+	app.ConsumerKeeper.SetStandaloneStakingKeeper(app.StakingKeeper)



    // change the slashing keeper dependency
    app.SlashingKeeper = slashingkeeper.NewKeeper(
        appCodec,
        legacyAmino,
        keys[slashingtypes.StoreKey],
-		app.StakingKeeper,
+		&app.ConsumerKeeper,  // ConsumerKeeper implements StakingKeeper interface
        authtypes.NewModuleAddress(govtypes.ModuleName).String(),
    )

    // register slashing module StakingHooks to the consumer keeper
+	app.ConsumerKeeper = *app.ConsumerKeeper.SetHooks(app.SlashingKeeper.Hooks())
+	consumerModule := consumer.NewAppModule(app.ConsumerKeeper, app.GetSubspace(consumertypes.ModuleName))

        // register the module with module manager
    // replace the x/staking module
    app.MM = module.NewManager(
        ...
-		sdkstaking.NewAppModule(appCodec, &app.StakingKeeper, app.AccountKeeper, app.BankKeeper, app.GetSubspace(stakingtypes.ModuleName)),
+		ccvstaking.NewAppModule(appCodec, *app.StakingKeeper, app.AccountKeeper, app.BankKeeper, app.GetSubspace(stakingtypes.ModuleName)),
        ...
    )
}
```

## Distribution

The `x/ccv/democracy/distribution` module allows the consumer chain to send rewards to the provider chain while retaining the logic of the `x/distribution` module for internal reward distribution to governators and their delegators.

### How it works

First, a percentage of the block rewards is sent to the provider chain, where is distributed only to opted-in validators and their delegators. 
Second, the remaining rewards get distributed to the consumer chain's governators and their delegators.
The percentage that is sent to the provider chain corresponds to `1 - ConsumerRedistributionFraction`.
For example, `ConsumerRedistributionFraction = "0.75"` means that the consumer chain retains 75% of the rewards, while 25% gets sent to the provider chain

### Integration

Change the wiring in `app.go`

```diff
import (
    ...
    distrkeeper "github.com/cosmos/cosmos-sdk/x/distribution/keeper"
    distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
    sdkdistr "github.com/cosmos/cosmos-sdk/x/distribution"

+   ccvdistr "github.com/cosmos/interchain-security/v4/x/ccv/democracy/distribution"
)

var (
    // replace sdk distribution AppModuleBasic
    ModuleBasics = module.NewBasicManager(
        auth.AppModuleBasic{},
        genutil.NewAppModuleBasic(genutiltypes.DefaultMessageValidator),
        bank.AppModuleBasic{},
        capability.AppModuleBasic{},
        ccvstaking.AppModuleBasic{}, // make sure you first swap the staking keeper
        mint.AppModuleBasic{},
-		sdkdistr.AppModuleBasic{},
+		ccvdistr.AppModuleBasic{},
    )
)

func NewApp(...) {
    ....

    app.DistrKeeper = distrkeeper.NewKeeper(
        appCodec,
        keys[distrtypes.StoreKey],
        app.AccountKeeper,
        app.BankKeeper,
        app.StakingKeeper,  // connect to sdk StakingKeeper
        consumertypes.ConsumerRedistributeName,
        authtypes.NewModuleAddress(govtypes.ModuleName).String(),
    )

    // register with the module manager
    app.MM = module.NewManager(
        ...
-		sdkdistr.NewAppModule(appCodec, app.DistrKeeper, app.AccountKeeper, app.BankKeeper, *app.StakingKeeper, authtypes.FeeCollectorName,     app.GetSubspace(distrtypes.ModuleName)),

+		ccvdistr.NewAppModule(appCodec, app.DistrKeeper, app.AccountKeeper, app.BankKeeper, *app.StakingKeeper, authtypes.FeeCollectorName, app.GetSubspace(distrtypes.ModuleName)),
        ccvstaking.NewAppModule(appCodec, *app.StakingKeeper, app.AccountKeeper, app.BankKeeper, app.GetSubspace(stakingtypes.ModuleName)),
        ...
    )
}
```
