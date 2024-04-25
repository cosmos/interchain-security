---
sidebar_position: 1
---

# Upgrading to ICS v5.0.0

This ICS version uses cosmos-sdk v0.50.x and ibc-go v8.x.

To migrate you application to cosmos-sdk v0.50.x please use this [guide](https://docs.cosmos.network/v0.50/build/migrations/upgrading).

To migrate your application to ibc-go v8.x.y please use the following guides:
 * [migrate ibc-go to v8.0.0](https://ibc.cosmos.network/main/migrations/v7-to-v8)
 * [migrate ibc-go to v8.1.0](https://ibc.cosmos.network/main/migrations/v8-to-v8_1)


ICS specific changes are outlined below.

Pre-requisite version for this upgrade: `v4.x`.

## Provider

### Keeper initialization

```diff
// app.go

app.ProviderKeeper = ibcproviderkeeper.NewKeeper(
    appCodec,
    keys[providertypes.StoreKey],
    app.GetSubspace(providertypes.ModuleName),
    scopedIBCProviderKeeper,
    app.IBCKeeper.ChannelKeeper,
-   app.IBCKeeper.PortKeeper
+   app.IBCKeeper.PortKeeper,
    app.IBCKeeper.ConnectionKeeper,
    app.IBCKeeper.ClientKeeper,
    app.StakingKeeper,
    app.SlashingKeeper,
    app.AccountKeeper,
    app.DistrKeeper,
    app.BankKeeper,
    *app.GovKeeper,
+   authtypes.NewModuleAddress(govtypes.ModuleName).String(),
+   authcodec.NewBech32Codec(sdk.GetConfig().GetBech32ValidatorAddrPrefix()),
+   authcodec.NewBech32Codec(sdk.GetConfig().GetBech32ConsensusAddrPrefix()),
    authtypes.FeeCollectorName,
)
```

* `authority` was added - requirement for executing `MsgUpdateParams`
    * uses `x/gov` module address by default

* `validatorAddressCodec` & `consensusAddressCodec` were added - they must match the bech32 address codec used by `x/auth`, `x/bank`, `x/staking`


### Protocol changes

#### Revert `AfterUnbondingInitiated`

`AfterUnbondingInitiated` behavior was reverted to [ICS@v1.2.0-multiden](https://github.com/cosmos/interchain-security/blob/v1.2.0-multiden/x/ccv/provider/keeper/hooks.go#L53)

The revert re-introduces an additional state check.

See this [issue](https://github.com/cosmos/interchain-security/issues/1045) for more context and the actions taken.


### Migration (v4 -> v5)

ConensusVersion was bumped to `5`.

The migration allows storing the provider module params in the `x/ccv/provider` module store instead of relying on legacy `x/param` store.

There are no special requirements for executing this migration.


### Additions

### MsgUpdateParams transaction

`x/gov` module account is selected as the default `authority`.

It is available when using `gov` CLI commands:

Drafting a proposal:

```shell
interchain-security-pd tx gov draft-proposal
# select "other"
# find and select "/interchain_security.ccv.provider.v1.MsgUpdateParams"
```

Submitting a proposal:

```shell
interchain-security-pd tx gov submit-proposal <proposal-message.json>
```

Example `proposal-message.json`:

```json
{
 "messages": [
  {
   "@type": "/interchain_security.ccv.provider.v1.MsgUpdateParams",
   "authority": "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn",
   "params": {
      "trusting_period_fraction": "0.66",
      "ccv_timeout_period": "2419200s",
      "init_timeout_period": "604800s",
      "vsc_timeout_period": "3024000s",
      "slash_meter_replenish_period": "3s",
      "slash_meter_replenish_fraction": "1.0",
      "consumer_reward_denom_registration_fee": {
          "denom": "stake",
          "amount": "10000000"
       },
      "blocks_per_epoch": "600"
   }
  }
 ],
 "metadata": "ipfs://CID",
 "deposit": "10000stake",
 "title": "Update Provider params",
 "summary": "Update Provider params",
 "expedited": false
}
```

###

When updating parameters **all** parameters fields must be specified. Make sure you are only changing parameters that you are interested in.

To avoid accidentally changing parameters you can first check the current on-chain provider params using:

```shell
interchain-security-pd q provider params -o json

{
  "template_client": {...},
  "trusting_period_fraction": "0.66",
  "ccv_timeout_period": "2419200s",
  "init_timeout_period": "604800s",
  "vsc_timeout_period": "3024000s",
  "slash_meter_replenish_period": "3s",
  "slash_meter_replenish_fraction": "1.0",
  "consumer_reward_denom_registration_fee": {
    "denom": "stake",
    "amount": "10000000"
  },
  "blocks_per_epoch": "600"
}
```

### Governance proposals

Submitting the following legacy proposals is still supported:

# Consumer addition proposal

```shell
interchain-security-pd tx gov submit-legacy-proposal consumer-addition <proposal_file.json>
```

# Consumer removal proposal

```shell
interchain-security-pd tx gov submit-legacy-proposal consumer-removal <proposal_file.json>
```

# Consumer addition proposal
```shell
interchain-security-pd tx gov submit-legacy-proposal change-reward-denoms <proposal_file.json>
```

You may also submit proposal messages above using `submit-proposal`.


## Consumer

### Keeper initialization

```diff
// pre-initialize ConsumerKeeper to satsfy ibckeeper.NewKeeper
app.ConsumerKeeper = ibcconsumerkeeper.NewNonZeroKeeper(
    appCodec,
    keys[ibcconsumertypes.StoreKey],
    app.GetSubspace(ibcconsumertypes.ModuleName),
)

app.IBCKeeper = ibckeeper.NewKeeper(
    appCodec,
    keys[ibchost.StoreKey],
    app.GetSubspace(ibchost.ModuleName),
    app.ConsumerKeeper,
    app.UpgradeKeeper,
    scopedIBCKeeper,
    authtypes.NewModuleAddress(govtypes.ModuleName).String(),
)

// initialize the actual consumer keeper
app.ConsumerKeeper = ibcconsumerkeeper.NewKeeper(
    appCodec,
    keys[ibcconsumertypes.StoreKey],
    app.GetSubspace(ibcconsumertypes.ModuleName),
    scopedIBCConsumerKeeper,
    app.IBCKeeper.ChannelKeeper,
-   &app.IBCKeeper.PortKeeper,
+   app.IBCKeeper.PortKeeper,
    app.IBCKeeper.ConnectionKeeper,
    app.IBCKeeper.ClientKeeper,
    app.SlashingKeeper,
    app.BankKeeper,
    app.AccountKeeper,
    &app.TransferKeeper,
    app.IBCKeeper,
    authtypes.FeeCollectorName,

    // make sure the authority address makes sense for your chain
    // the exact module account may differ depending on your setup (x/gov, x/admin or custom module)
    // for x/ccv/democracy using the x/gov module address is correct
    // if you don't have a way of updating consumer params you may still use the line below as it will have no affect
+   authtypes.NewModuleAddress(govtypes.ModuleName).String(),
    
    // add address codecs  
+   authcodec.NewBech32Codec(sdk.GetConfig().GetBech32ValidatorAddrPrefix()),
+   authcodec.NewBech32Codec(sdk.GetConfig().GetBech32ConsensusAddrPrefix()),
)
```


* `authority` was added - requirement for executing `MsgUpdateParams`
    * make sure the authority address makes sense for your chain   
    * the exact module account may differ depending on your setup (`x/gov`, `x/admin` or custom module)
    * for `x/ccv/democracy` using the `x/gov` module address is correct
    * if you don't have a way of updating consumer params you may use `authtypes.NewModuleAddress(govtypes.ModuleName).String()` (has no effect on functionality)

* `validatorAddressCodec` & `consensusAddressCodec` were added - they must match the bech32 address codec used by `x/auth`, `x/bank`, `x/staking`
 

### Additions

#### `MsgUpdateParams` transaction

**This functionality is not supported on `x/ccv/consumer` without additional configuration.**
* if you are using `x/ccv/democracy` the feature is supported out of the box
* if you are using custom logic for changing consumer params, please update your code by providing the appropriate `authority` module account during `ConsumerKeeper` initialization in `app.go`.
    
**You must add `"/interchain_security.ccv.consumer.v1.MsgUpdateParams"` to your parameters whitelist to be able to change `ccvconsumer` parameters via governance.**

It is available when using `gov` CLI commands:

Drafting a proposal:

```shell
interchain-security-cd tx gov draft-proposal
# select "other"
# find and select "/interchain_security.ccv.consumer.v1.MsgUpdateParams"
```

Submitting a proposal:
* **this proposal cannot be executed on chains without access to `x/gov` or other modules for managing governance**

```shell

interchain-security-cdd tx gov submit-proposal <proposal-message.json>

```

Example `proposal-message.json`.
```json
{
 "messages": [
  {
   "@type": "/interchain_security.ccv.consumer.v1.MsgUpdateParams",
   "authority": "consumer10d07y265gmmuvt4z0w9aw880jnsr700jlh7295",
   "params": {
    "enabled": true,
    "blocks_per_distribution_transmission": "20",
    "distribution_transmission_channel": "channel-1",
    "provider_fee_pool_addr_str": "",
    "ccv_timeout_period": "2419200s",
    "transfer_timeout_period": "3000s",
    "consumer_redistribution_fraction": "0.75",
    "historical_entries": "10000",
    "unbonding_period": "1209600s",
    "soft_opt_out_threshold": "0.05",
    "reward_denoms": [],
    "provider_reward_denoms": [],
    "retry_delay_period": "3000s"
   }
  }
 ],
 "metadata": "ipfs://CID",
 "deposit": "1000uatom",
 "title": "Update Consumer Params -- change transfer_timeout_period to 3000s",
 "summary": "Test Update Consumer Params",
 "expedited": false
}
```

When updating parameters **all** parameters fields must be specified. Make sure you are only changing parameters that you are interested in.

To avoid accidentally changing parameters you can first check the current on-chain consumer params using:

```shell
interchain-security-pd q ccvconsumer params -o json
```


#### Params Query

Consumer params query was added:
```shell
interchain-security-cd q ccvconsumer params -o json

{
  "params": {
    "enabled": true,
    "blocks_per_distribution_transmission": "1000",
    "distribution_transmission_channel": "",
    "provider_fee_pool_addr_str": "",
    "ccv_timeout_period": "2419200s",
    "transfer_timeout_period": "3600s",
    "consumer_redistribution_fraction": "0.75",
    "historical_entries": "10000",
    "unbonding_period": "1209600s",
    "soft_opt_out_threshold": "0.05",
    "reward_denoms": [],
    "provider_reward_denoms": [],
    "retry_delay_period": "3600s"
  }
}
```


### Migration (v2 -> v3)
ConensusVersion was bumped to `3`.

The migration allows storing the consumer module params in the `x/ccv/consumer` module store instead of relying on legacy `x/param` store.

There are no special requirements for executing this migration.


### Interface method changes
Consumer methods were changed to match the cosmos-sdk `StakingKeeper` interface.
You will not need to change your code, unless you are using the `ConsumerKeeper` inside custom tests or you have developed custom app functionality that relies on `ConsumerKeeper`.

Please check the list below if you are using any of the consumer methods:
```go
type StakingKeeper interface {
  UnbondingTime(ctx context.Context) (time.Duration, error)
  GetValidatorByConsAddr(ctx context.Context, consAddr sdk.ConsAddress) (stakingtypes.Validator, error)
  GetLastValidatorPower(ctx context.Context, operator sdk.ValAddress) (int64, error)
  Jail(context.Context, sdk.ConsAddress) error // jail a validator
  Slash(ctx context.Context, consAddr sdk.ConsAddress, infractionHeight, power int64, slashFactor math.LegacyDec) (math.Int, error)
  SlashWithInfractionReason(ctx context.Context, consAddr sdk.ConsAddress, infractionHeight, power int64, slashFactor math.LegacyDec, infraction stakingtypes.Infraction) (math.Int, error)
  Unjail(ctx context.Context, addr sdk.ConsAddress) error
  GetValidator(ctx context.Context, addr sdk.ValAddress) (stakingtypes.Validator, error)
  IterateLastValidatorPowers(ctx context.Context, cb func(addr sdk.ValAddress, power int64) (stop bool)) error
  IterateValidators(ctx context.Context, f func(index int64, validator stakingtypes.ValidatorI) (stop bool)) error
  Validator(ctx context.Context, addr sdk.ValAddress) (stakingtypes.ValidatorI, error)
  IsValidatorJailed(ctx context.Context, addr sdk.ConsAddress) (bool, error)
  ValidatorByConsAddr(ctx context.Context, consAddr sdk.ConsAddress) (stakingtypes.ValidatorI, error)
  Delegation(ctx context.Context, addr sdk.AccAddress, valAddr sdk.ValAddress) (stakingtypes.DelegationI, error)
  MaxValidators(ctx context.Context) (uint32, error)
}
```

The consumer implements the `StakingKeeper` interface shown above.

## Democracy

Changes in `Consumer` also apply to `Democracy`. 

Democracy `x/staking`, `x/distribution` and `x/gov` were updated to reflect changes in `cosmos-sdk v0.50.x`.

There were no notable changes arising to the module functionality aside from conforming to `cosmos-sdk v0.50.x`.


## Note:
You must add `"/interchain_security.ccv.consumer.v1.MsgUpdateParams"` to your parameters whitelist to be able to change `consumer` parameters via governance.
