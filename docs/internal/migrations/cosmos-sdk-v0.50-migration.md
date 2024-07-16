# cosmos-sdk v0.50.x internal upgrade doc

This file lists various changes that were needed when upgrading from cosmos-sdk v0.47.x -> v0.50.x.

Upgrade instructions used:
* https://docs.cosmos.network/v0.50/migrations/upgrading
* https://ibc.cosmos.network/main/migrations/v7-to-v8.html
* https://ibc.cosmos.network/main/migrations/v8-to-v8_1

## Proto files
Some proto files needed to be updated to reflect changes required for cosmos-sdk v50.

## Provider proto changes

### proto/interchain_security/ccv/provider/v1/tx.proto

Added rpc methods and message types to support v50 governance (`submit-proposal`)
* `rpc ConsumerAddition`
* `rpc ConsumerRemoval`
* `message MsgUpdateParams`
* `message MsgConsumerAddition`
* `message MsgConsumerRemoval`
* `message MsgChangeRewardDenoms`
* `message MsgUpdateParams`


Update existing messages with `option (cosmos.msg.v1.signer) = "signer"` so they are considered as Tx messages by v50.
* `message MsgAssignConsumerKey`

`message MsgUpdateParams` was added to support updating params via governance.


## Generating protos with updated dependencies:

```
# update Makefile containerProtoVersion to latest (v0.14.0)
cd proto
# update buf.yml
buf mod update
cd ..
make proto-gen
```

### Steps for upgrading cosmos-sdk and ibc-go
Key dependencies:
* `cosmos-sdk@v0.50.4`
* `ibc-go/v8@v8.1.0`
* `ibc-go/modules/capability@v1.0.0`

```shell
go get github.com/cosmos/cosmos-sdk@v0.50.4
go get github.com/cosmos/ibc-go/v8@v8.1.0
go get github.com/cosmos/ibc-go/modules/capability@v1.0.0-rc5
```

`ibc-go/v8` is using the `x/capability` module that lives in `github.com/cosmos/ibc-go/modules/capability`.
* this module was added after all the file imports were changed for ibc-go (from v7 -> v8) to avoid weird import behaviour

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
* cosmossdk.io/x/upgrade/client -> no longer exists and not needed
* github.com/cosmos/ibc-go/v7/modules/core/02-client/client -> these gov handlers no longer exist (deprecated)

### Math search & replace
* use `math.LegacyDec` instead of `sdk.Dec` and other types
	* eg. `sdk.NewDecFromStr`, `sdktypes.NewDecFromStr`, `sdk.NewDec`
	* `sdk.ZeroDec` -> `math.LegacyZeroDec`
	* `sdk.NewDecFromInt` -> `math.LegacyNewDecFromInt` 
	* `sdk.MustNewDecFromStr` -> `math.LegacyMustNewDecFromStr`
	* `sdk.NewDecFromInt` -> `math.LegacyNewDecFromInt`
	* `sdk.OneDec` -> `math.LegacyOneDec`
	* `sdk.NewDecWithPrec` -> `math.LegacyNewDecWithPrec`
	* also update all function defintions that are using them

* use `math.NewInt` instead of `sdk.NewInt`
	* `sdktypes.NewInt`,
	* `sdktypes.ZeroInt` -> `math.ZeroInt`
	* also update all dunction definitions that are using them

## Genesis
`expedited_voting_period` was introduced. All functions using gov proposals needed to be updated to support `expedited_voting_period (bool)`


## Governance proposals (provider)
Legacy proposal handlers were modified to reflect cosmos-sdk v0.50.x changes. Legacy proposals are still supported.

## Query & Tx
AutoCLI usage was added.

To use AutoCLI all Txs must be annotated with  `option (cosmos.msg.v1.service) = true`;


## ICS code changes

## migrate x/staking & x/slashing interfaces

New interfaces match x/staking and x/slashing on cosmos-sdk v0.50.x.

```go
type StakingKeeper interface {
	GetValidatorUpdates(ctx context.Context) ([]abci.ValidatorUpdate, error)
	UnbondingCanComplete(ctx context.Context, id uint64) error
	UnbondingTime(ctx context.Context) (time.Duration, error)
	GetValidatorByConsAddr(ctx context.Context, consAddr sdk.ConsAddress) (stakingtypes.Validator, error)
	GetLastValidatorPower(ctx context.Context, operator sdk.ValAddress) (int64, error)
	Jail(context.Context, sdk.ConsAddress) error // jail a validator
	Slash(ctx context.Context, consAddr sdk.ConsAddress, infractionHeight, power int64, slashFactor math.LegacyDec) (math.Int, error)
	SlashWithInfractionReason(ctx context.Context, consAddr sdk.ConsAddress, infractionHeight, power int64, slashFactor math.LegacyDec, infraction stakingtypes.Infraction) (math.Int, error)
	SlashUnbondingDelegation(ctx context.Context, unbondingDelegation stakingtypes.UnbondingDelegation, infractionHeight int64, slashFactor math.LegacyDec) (math.Int, error)
	SlashRedelegation(ctx context.Context, srcValidator stakingtypes.Validator, redelegation stakingtypes.Redelegation, infractionHeight int64, slashFactor math.LegacyDec) (math.Int, error)
	Unjail(ctx context.Context, addr sdk.ConsAddress) error
	GetValidator(ctx context.Context, addr sdk.ValAddress) (stakingtypes.Validator, error)
	IterateLastValidatorPowers(ctx context.Context, cb func(addr sdk.ValAddress, power int64) (stop bool)) error
	PowerReduction(ctx context.Context) math.Int
	PutUnbondingOnHold(ctx context.Context, id uint64) error
	IterateValidators(ctx context.Context, f func(index int64, validator stakingtypes.ValidatorI) (stop bool)) error
	Validator(ctx context.Context, addr sdk.ValAddress) (stakingtypes.ValidatorI, error)
	IsValidatorJailed(ctx context.Context, addr sdk.ConsAddress) (bool, error)
	ValidatorByConsAddr(ctx context.Context, consAddr sdk.ConsAddress) (stakingtypes.ValidatorI, error)
	Delegation(ctx context.Context, addr sdk.AccAddress, valAddr sdk.ValAddress) (stakingtypes.DelegationI, error)
	MaxValidators(ctx context.Context) (uint32, error)
	GetLastTotalPower(ctx context.Context) (math.Int, error)
	GetLastValidators(ctx context.Context) ([]stakingtypes.Validator, error)
	BondDenom(ctx context.Context) (string, error)
	GetUnbondingDelegationsFromValidator(ctx context.Context, valAddr sdk.ValAddress) ([]stakingtypes.UnbondingDelegation, error)
	GetRedelegationsFromSrcValidator(ctx context.Context, valAddr sdk.ValAddress) ([]stakingtypes.Redelegation, error)
	GetUnbondingType(ctx context.Context, id uint64) (stakingtypes.UnbondingType, error)
}

type SlashingKeeper interface {
	JailUntil(context.Context, sdk.ConsAddress, time.Time) error // called from provider keeper only
	GetValidatorSigningInfo(context.Context, sdk.ConsAddress) (slashingtypes.ValidatorSigningInfo, error)
	SetValidatorSigningInfo(context.Context, sdk.ConsAddress, slashingtypes.ValidatorSigningInfo) error
	DowntimeJailDuration(context.Context) (time.Duration, error)
	SlashFractionDowntime(context.Context) (math.LegacyDec, error)
	SlashFractionDoubleSign(context.Context) (math.LegacyDec, error)
	Tombstone(context.Context, sdk.ConsAddress) error
	IsTombstoned(context.Context, sdk.ConsAddress) bool
}
```

Changes to these interfaces required changing unit and integration test assertions. Almost all methods are now returning an `error`. Previously, almost none of the methods were returning errors.

## Refactoring ICS keepers

### Context
Instead of using `sdk.Context` we need to use `context.Context`.

Example:
```go
func (k Keeper) Logger(ctx context.Context) log.Logger {
	sdkCtx := sdk.UnwrapSDKContext(ctx)  // we accept context.Context and unwrap it
	return sdkCtx.Logger().With("module", "x/"+ibchost.ModuleName+"-"+types.ModuleName)
}
```

Remaining work for future upgrades:
* allow store access via `k.storeService.OpenKVStore(ctx)` instead of `ctx.KVStore(k.storeKey)`.


### validator.GetConsAddr()
Cannot do `sdk.ConsAddress(validatorConsumerAddrs.ConsumerAddr).Equals(consensusAddr)` because `.Equals()` now takes a `sdk.Address` interface type.
Change to `sdk.ConsAddress(validatorConsumerAddrs.ConsumerAddr).Equals(sdk.ConsAddress(consensusAddr))`



### ICS keepers initialization
```go
type Keeper struct {
	// the address capable of executing a MsgUpdateParams message. Typically, this
	// should be the x/gov module account.
	authority string

    // address codecs were added
    validatorAddressCodec addresscodec.Codec
	consensusAddressCodec addresscodec.Codec
}

// GetAuthority returns the module's authority.
func (k Keeper) GetAuthority() string {
	return k.authority
}

```


### Hooks
In v0.50.x hooks are setup in the `keeper.go`

```go
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

`sdk.Handler` no longer exists and needs to be replaced with `baseapp.MsgServiceHandler
```diff
// x/ccv/provider/handler.go
-func NewHandler(k *keeper.Keeper) sdk.Handler {
-	msgServer := keeper.NewMsgServerImpl(k)
+func NewHandler(k *keeper.Keeper) sdk.Handler {
+   msgServer := keeper.NewMsgServerImpl(k)
	// ...
}
```


## validator.GetOperator() has different return type
Previously `validator.GetOperator()` was returning `sdk.ValAddress`. In v0.50.x it returns a `string`.

Additional processing is required when fetching validator operator address:
```diff
-slashedVal.GetOperator()
+providerKeeper.ValidatorAddressCodec().StringToBytes(slashedVal.GetOperator())
```

Example:
```diff
// from integration tests
-lastValPower := providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), slashedVal.GetOperator())
+slashedValOperator, err := providerKeeper.ValidatorAddressCodec().StringToBytes(slashedVal.GetOperator()) // must get the addr bytes first
+s.Require().NoError(err)
+lastValPower, err := providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), slashedValOperator)
```


## evidencekeeper equivocation handling was made private

```diff
type EvidenceKeeper interface {
-	HandleEquivocationEvidence(ctx sdk.Context, evidence *evidencetypes.Equivocation)
+	handleEquivocationEvidence(ctx sdk.Context, evidence *evidencetypes.Equivocation)
}
```

This method is only used in integration testing. To preserve testing, the method was copied and modified to fit the testing use case.
```go
// copy of the function from slashing/keeper.go
// in cosmos-sdk v0.50.x the function HandleEquivocationEvidence is not exposed (it was exposed for versions <= v0.47.x)
// https://github.com/cosmos/cosmos-sdk/blob/v0.50.4/x/evidence/keeper/infraction.go#L27
func handleEquivocationEvidence(ctx context.Context, k integration.ConsumerApp, evidence *types.Equivocation) error {
	sdkCtx := sdk.UnwrapSDKContext(ctx)
	slashingKeeper := k.GetTestSlashingKeeper().(slashingkeeper.Keeper)
	evidenceKeeper := k.GetTestEvidenceKeeper()
	consAddr := evidence.GetConsensusAddress(k.GetConsumerKeeper().ConsensusAddressCodec())

	validator, err := k.GetConsumerKeeper().ValidatorByConsAddr(ctx, consAddr)
	if err != nil {
		return err
	}
	if validator == nil || validator.IsUnbonded() {
		return nil
	}

	if len(validator.GetOperator()) != 0 {
		if _, err := slashingKeeper.GetPubkey(ctx, consAddr.Bytes()); err != nil {
			return nil
		}
	}

	// calculate the age of the evidence
	infractionHeight := evidence.GetHeight()
	infractionTime := evidence.GetTime()
	ageDuration := sdkCtx.BlockHeader().Time.Sub(infractionTime)
	ageBlocks := sdkCtx.BlockHeader().Height - infractionHeight

	// Reject evidence if the double-sign is too old. Evidence is considered stale
	// if the difference in time and number of blocks is greater than the allowed
	// parameters defined.
	cp := sdkCtx.ConsensusParams()
	if cp.Evidence != nil {
		if ageDuration > cp.Evidence.MaxAgeDuration && ageBlocks > cp.Evidence.MaxAgeNumBlocks {
			return nil
		}
	}

	if ok := slashingKeeper.HasValidatorSigningInfo(ctx, consAddr); !ok {
		panic(fmt.Sprintf("expected signing info for validator %s but not found", consAddr))
	}

	// ignore if the validator is already tombstoned
	if slashingKeeper.IsTombstoned(ctx, consAddr) {
		return nil
	}

	distributionHeight := infractionHeight - sdk.ValidatorUpdateDelay
	slashFractionDoubleSign, err := slashingKeeper.SlashFractionDoubleSign(ctx)
	if err != nil {
		return err
	}

	err = slashingKeeper.SlashWithInfractionReason(
		ctx,
		consAddr,
		slashFractionDoubleSign,
		evidence.GetValidatorPower(), distributionHeight,
		stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN,
	)
	if err != nil {
		return err
	}

	// Jail the validator if not already jailed. This will begin unbonding the
	// validator if not already unbonding (tombstoned).
	if !validator.IsJailed() {
		err = slashingKeeper.Jail(ctx, consAddr)
		if err != nil {
			return err
		}
	}

	err = slashingKeeper.JailUntil(ctx, consAddr, types.DoubleSignJailEndTime)
	if err != nil {
		return err
	}

	err = slashingKeeper.Tombstone(ctx, consAddr)
	if err != nil {
		return err
	}
	return evidenceKeeper.Evidences.Set(ctx, evidence.Hash(), evidence)
}

```

