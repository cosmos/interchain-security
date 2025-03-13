# Upgrading Interchain Security

## v6.4.x

### Provider

Upgrading a provider from `v6.2.x / v6.3.x` requires state migrations. The following migrators should be added to the upgrade handler of the provider chain:

```golang
// Initializes infraction parameters for each active consumer. During slashing and jailing of validators for misbehavior on the consumer chain, the parameters defined for that specific consumer will be used. Initially, default values are set, which can later be customized for each consumer as needed.
func SetConsumerInfractionParams(ctx sdk.Context, pk providerkeeper.Keeper) error {
	infractionParameters := DefaultInfractionParams()

	activeConsumerIds := pk.GetAllActiveConsumerIds(ctx)
	for _, consumerId := range activeConsumerIds {
		if err := pk.SetInfractionParameters(ctx, consumerId, infractionParameters); err != nil {
			return err
		}
	}

	return nil
}

func DefaultInfractionParams() providertypes.InfractionParameters {
	return providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  time.Duration(1<<63 - 1),        // the largest value a time.Duration can hold 9223372036854775807 (approximately 292 years)
			SlashFraction: math.LegacyNewDecWithPrec(5, 2), // 0.05
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  600 * time.Second,
			SlashFraction: math.LegacyNewDec(0), // no slashing for downtime on the consumer
		},
	}
}
```

## v6.3.x

Upgrading from `v6.2.0` will not require state migration. To upgrade from lower versions, please check the sections below.

## v6.2.x

### Consumer

Upgrading a consumer from v4.4.x to v4.5.x and from v5.x or v6.1.x to v6.2.x requires state migrations. The following migrators should be added to the upgrade handler of the consumer chain:


```go
// InitializeConsumerId sets the consumer Id parameter in the consumer module,
// to the consumer id for which the consumer is registered on the provider chain.
// The consumer id can be obtained in by querying the provider, e.g. by using the
// QueryConsumerIdFromClientId query.
func InitializeConsumerId(ctx sdk.Context, consumerKeeper consumerkeeper.Keeper) {
	params := consumerKeeper.GetConsumerParams(ctx)
	params.ConsumerId = ConsumerId
	consumerKeeper.SetParams(ctx, params)
}
```

## [v6.1.x](https://github.com/cosmos/interchain-security/releases/tag/v6.1.0)

Upgrading from `v6.0.0` will not require state migration.


## [v6.0.x](https://github.com/cosmos/interchain-security/releases/tag/v6.0.0)

### Provider

Upgrading a provider from v5.1.x requires state migrations. The following migrators should be added to the upgrade handler of the provider chain:

```go
// InitializeMaxProviderConsensusParam initializes the MaxProviderConsensusValidators parameter.
// It is set to 180, which is the current number of validators participating in consensus on the Cosmos Hub.
// This parameter will be used to govern the number of validators participating in consensus on the Cosmos Hub,
// and takes over this role from the MaxValidators parameter in the staking module.
func InitializeMaxProviderConsensusParam(ctx sdk.Context, providerKeeper providerkeeper.Keeper) {
	params := providerKeeper.GetParams(ctx)
	params.MaxProviderConsensusValidators = NewMaxProviderConsensusValidators
	providerKeeper.SetParams(ctx, params)
}
```

```go
// SetMaxValidators sets the MaxValidators parameter in the staking module to 200,
// which is the current number of 180 plus 20.
// This is done in concert with the introduction of the inactive-validators feature
// in Interchain Security, after which the number of validators
// participating in consensus on the Cosmos Hub will be governed by the
// MaxProviderConsensusValidators parameter in the provider module.
func SetMaxValidators(ctx sdk.Context, stakingKeeper stakingkeeper.Keeper) error {
	params, err := stakingKeeper.GetParams(ctx)
	if err != nil {
		return err
	}
	params.MaxValidators = NewMaxValidators
	return stakingKeeper.SetParams(ctx, params)
}
```

```go
// InitializeLastProviderConsensusValidatorSet initializes the last provider consensus validator set
// by setting it to the first 180 validators from the current validator set of the staking module.
func InitializeLastProviderConsensusValidatorSet(ctx sdk.Context, providerKeeper providerkeeper.Keeper, stakingKeeper stakingkeeper.Keeper) error {
	vals, err := stakingKeeper.GetBondedValidatorsByPower(ctx)
	if err != nil {
		return err
	}
	// cut the validator set to the first 180 validators
	if len(vals) > NewMaxProviderConsensusValidators {
		vals = vals[:NewMaxProviderConsensusValidators]
	}
	// create consensus validators for the staking validators
	lastValidators := []providertypes.ConsensusValidator{}
	for _, val := range vals {
		consensusVal, err := providerKeeper.CreateProviderConsensusValidator(ctx, val)
		if err != nil {
			return err
		}

		lastValidators = append(lastValidators, consensusVal)
	}
	return providerKeeper.SetLastProviderConsensusValSet(ctx, lastValidators)
}
```

```go
// SetICSConsumerMetadata sets the metadata for launched consumer chains
func SetICSConsumerMetadata(ctx sdk.Context, providerKeeper providerkeeper.Keeper) error {
	for _, consumerID := range providerKeeper.GetAllActiveConsumerIds(ctx) {
		phase := providerKeeper.GetConsumerPhase(ctx, consumerID)
		if phase != providertypes.CONSUMER_PHASE_LAUNCHED {
			continue
		}
		chainID, err := providerKeeper.GetConsumerChainId(ctx, consumerID)
		if err != nil {
			ctx.Logger().Error(
				fmt.Sprintf("cannot get chain ID for consumer chain, consumerID(%s)", consumerID),
			)
			continue
		}

		// example of setting the metadata for Stride
		if chainID == "stride-1" {
			metadata := providertypes.ConsumerMetadata{
				Name: "Stride",
				Description: "Description",
				Metadata: "Metadata",
			}
			err = providerKeeper.SetConsumerMetadata(ctx, consumerID, metadata)
			if err != nil {
				ctx.Logger().Error(
					fmt.Sprintf("cannot set consumer metadata, consumerID(%s), chainID(%s): %s", consumerID, chainID, err.Error()),
				)
				continue
			}
		}
	}
}
```

```go
// MigrateICSProposals migrates deprecated proposals
func MigrateICSProposals(ctx sdk.Context, msgServer providertypes.MsgServer, providerKeeper providerkeeper.Keeper, govKeeper govkeeper.Keeper) error {
	proposals := []govtypesv1.Proposal{}
	err := govKeeper.Proposals.Walk(ctx, nil, func(key uint64, proposal govtypesv1.Proposal) (stop bool, err error) {
		proposals = append(proposals, proposal)
		return false, nil // go through the entire collection
	})
	if err != nil {
		return errorsmod.Wrapf(err, "iterating through proposals")
	}
	for _, proposal := range proposals {
		err := MigrateICSLegacyProposal(ctx, msgServer, providerKeeper, govKeeper, proposal)
		if err != nil {
			return errorsmod.Wrapf(err, "migrating legacy proposal %d", proposal.Id)
		}

		err = MigrateICSProposal(ctx, msgServer, providerKeeper, govKeeper, proposal)
		if err != nil {
			return errorsmod.Wrapf(err, "migrating proposal %d", proposal.Id)
		}
	}
	return nil
}

// MigrateICSLegacyProposal migrates the following proposals 
// - ConsumerAdditionProposal
// - ConsumerRemovalProposal
// - ConsumerModificationProposal
// - ChangeRewardDenomsProposal

// MigrateICSProposal migrates the following proposals 
// - MsgConsumerAddition
// - MsgConsumerRemoval
// - MsgConsumerModification
```

For an example, see the [Gaia v20 upgrade handler](https://github.com/cosmos/gaia/blob/e4656093955578b2efa6e8c2ea8dd8823008bba3/app/upgrades/v20/upgrades.go#L43).  

### Consumer

Upgrading the consumer from `v5.0.0` or `v5.2.0` will not require state migration.

## [v5.1.x](https://github.com/cosmos/interchain-security/releases/tag/v5.1.0)

### Provider

***Note that providers using v5.0.0 cannot upgrade to v5.1.0 cleanly***

Providers using versions `v4.0.x`, `v4.1.x`, `v4.2.x`, `v4.3.x` and `v4.4.x` can upgrade to `v5.1.0`.

Upgrading from `v4.x` to `v5.1.0` will upgrade the provider `consensus version` to 7.

Upgrade code will be executed automatically during the upgrade procedure.

### Consumer

Upgrading the consumer from `v5.0.0` to `v5.1.0` will not require state migration.

This guide provides instructions for upgrading to specific versions of Replicated Security.

## [v5.0.0](https://github.com/cosmos/interchain-security/releases/tag/v5.0.0)

### Provider

***Note that providers should not be using this release***

v5.0.0 was a **consumer only release**.

### Consumer

Upgrading the consumer from `v4.x` to `v5.0.0` will require state migrations.

Consumer versions `v4.0.x`, `v4.1.x`, `v4.2.x`, `v4.3.x` and `v4.4.x` can cleanly be upgraded to `v5.0.0`.

Upgrade code will be executed automatically during the upgrade procedure.

## [v4.4.x](https://github.com/cosmos/interchain-security/releases/tag/v4.4.0)

### Provider

***Note that provider chains should not use this version of ICS***

### Consumer

Upgrading the consumer from `v4.0.0` to `v4.4.0` will not require state migration.

This guide provides instructions for upgrading to specific versions of Replicated Security.

## [v4.3.x](https://github.com/cosmos/interchain-security/releases/tag/v4.3.0)

### Provider

Upgrading a provider from `v4.2.0` to `v4.3.0` requires state migrations that will be done automatically via the upgrade module.

### Consumer

***Note that consumer chains should not use this version of ICS***

## [v4.2.x](https://github.com/cosmos/interchain-security/releases/tag/v4.2.0)

### Provider

Upgrading a provider from `v4.1.0` or `v4.1.0-lsm` to `v4.2.0` or `v4.2.0-lsm` requires state migrations, see relevant pull request [here](https://github.com/cosmos/interchain-security/pull/1809)
for the corresponding migrators.

### Consumer

***Note that consumer chains should not use this version of ICS***

## [v4.1.x](https://github.com/cosmos/interchain-security/releases/tag/v4.1.0-rc2) and [v4.1.x-lsm](https://github.com/cosmos/interchain-security/releases/tag/v4.1.0-lsm-rc2)

### Provider

Upgrading a provider from `v4.0.0` to `v4.1.0` or `v4.1.0-lsm` requires state migrations, see relevant pull request [here](https://github.com/cosmos/interchain-security/pull/1762),
as well as the corresponding migrators [here](https://github.com/cosmos/interchain-security/blob/release/v4.1.x/x/ccv/provider/migrations/migrator.go#L38) and [here](https://github.com/cosmos/interchain-security/blob/release/v4.1.x-lsm/x/ccv/provider/migrations/migrator.go#L38).
Apart from running the ICS migrators, the provider chain also needs to initialize the `ConsumerValSet` for all existing consumer chains to ensure correct validator set replication.
To do so, the following code should be added to the upgrade handler of the provider chain:
```go
func InitICSEpochs(ctx sdk.Context, pk providerkeeper.Keeper, sk stakingkeeper.Keeper) error {
	ctx.Logger().Info("Initializing ICS epochs...")

	// get the bonded validators from the staking module
	bondedValidators := sk.GetLastValidators(ctx)

	for _, chain := range pk.GetAllConsumerChains(ctx) {
		chainID := chain.ChainId
		valset := pk.GetConsumerValSet(ctx, chainID)
		if len(valset) > 0 {
			ctx.Logger().Info("consumer chain `%s` already has the valset initialized", chainID)
		} else {
			// init valset for consumer with chainID
			nextValidators := pk.ComputeNextEpochConsumerValSet(ctx, chainID, bondedValidators)
			pk.SetConsumerValSet(ctx, chainID, nextValidators)
		}
	}

	ctx.Logger().Info("Finished initializing ICS epochs")
	return nil
}
```

### Consumer

***Note that consumer chains can upgrade directly from `v4.0.0` to `v4.1.0`.***

## [v4.0.x](https://github.com/cosmos/interchain-security/tree/release/v4.0.x)

`v4.0.x` sets the minimum required version of Go to `1.21`, see https://github.com/cosmos/interchain-security/blob/release/v4.0.x/go.mod#L3.

### Provider

Upgrading a provider from `v3.3.0` to `v4.0.0` will require state migrations, see https://github.com/cosmos/interchain-security/blob/release/v4.0.x/x/ccv/provider/migrations/migrator.go#L31.

### Consumer

***Note that consumer chains can upgrade directly from `v3.1.0` to `v4.0.0`.***

Upgrading a consumer from `v3.2.0` to `v4.0.0` will not require state migration, however, upgrading directly from `v3.1.0` to `v4.0.0` will require state migrations, see https://github.com/cosmos/interchain-security/blob/release/v4.0.x/x/ccv/consumer/keeper/migrations.go#L22.

In addition, the following migration needs to be added to the upgrade handler of the consumer chain:
```golang
func migrateICSOutstandingDowntime(ctx sdk.Context, keepers *upgrades.UpgradeKeepers) error {
	ctx.Logger().Info("Migrating ICS outstanding downtime...")

	downtimes := keepers.ConsumerKeeper.GetAllOutstandingDowntimes(ctx)
	for _, od := range downtimes {
		consAddr, err := sdk.ConsAddressFromBech32(od.ValidatorConsensusAddress)
		if err != nil {
			return err
		}
		keepers.ConsumerKeeper.DeleteOutstandingDowntime(ctx, consAddr)
	}

	ctx.Logger().Info("Finished ICS outstanding downtime")

	return nil
}
```

## [v3.3.x](https://github.com/cosmos/interchain-security/tree/release/v3.2.x)

### Provider

Upgrading the provider from `v2.x.y` to `v3.3.0` will not require state migration.

## [v3.2.x](https://github.com/cosmos/interchain-security/tree/release/v3.2.x)

`v3.2.0` bumps IBC to `v7.3`. As a result, `legacy_ibc_testing` is not longer required and was removed, see https://github.com/cosmos/interchain-security/pull/1185. This means that when upgrading to `v3.2.0`, any customized tests relying on `legacy_ibc_testing` need to be updated.

### Consumer

Upgrading the consumer from either `v3.0.0` or `v3.1.0` to `v3.2.0` will require state migrations, see https://github.com/cosmos/interchain-security/blob/release/v3.2.x/x/ccv/consumer/keeper/migration.go#L25.

## [v3.0.x](https://github.com/cosmos/interchain-security/releases/tag/v3.0.0-rc0)

### Upgrading to Cosmos SDK 0.47

The following should be considered as complementary to [Cosmos SDK v0.47 UPGRADING.md](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0-rc2/UPGRADING.md).

#### Protobuf

Protobuf code generation, linting and formatting have been updated to leverage the `ghcr.io/cosmos/proto-builder:0.11.5` docker container. Replicated Security protobuf definitions are now packaged and published to [buf.build/cosmos/interchain-security](https://buf.build/cosmos/interchain-security) via CI workflows. The `third_party/proto` directory has been removed in favour of dependency management using [buf.build](https://docs.buf.build/introduction).

#### App modules

Legacy APIs of the `AppModule` interface have been removed from ccv modules. For example, for

```diff
- // Route implements the AppModule interface
- func (am AppModule) Route() sdk.Route {
-     return sdk.Route{}
- }
-
- // QuerierRoute implements the AppModule interface
- func (AppModule) QuerierRoute() string {
-     return types.QuerierRoute
- }
-
- // LegacyQuerierHandler implements the AppModule interface
- func (am AppModule) LegacyQuerierHandler(*codec.LegacyAmino) sdk.Querier {
-     return nil
- }
-
- // ProposalContents doesn't return any content functions for governance proposals.
- func (AppModule) ProposalContents(_ module.SimulationState) []simtypes.WeightedProposalContent {
-     return nil
- }
```

#### Imports

Imports for ics23 have been updated as the repository have been migrated from confio to cosmos.

```diff
import (
    // ...
-   ics23 "github.com/confio/ics23/go"
+   ics23 "github.com/cosmos/ics23/go"
    // ...
)
```

Imports for gogoproto have been updated.

```diff
import (
    // ...
-   "github.com/gogo/protobuf/proto"
+   "github.com/cosmos/gogoproto/proto"
    // ...
)
```

## [v2.0.x](https://github.com/cosmos/interchain-security/releases/tag/v2.0.0)

### Provider

Upgrading a provider from `v1.1.0-multiden` to `v2.0.0` will require state migrations. See [migration.go](https://github.com/cosmos/interchain-security/blob/v2.0.0/x/ccv/provider/keeper/migration.go).

### Consumer

Upgrading a consumer from `v1.2.0-multiden` to `v2.0.0` will NOT require state migrations.