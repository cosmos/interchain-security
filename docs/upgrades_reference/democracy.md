# Democracy modules changes

## Distribution
Module now implements `appmodule.HasBeginBlocker`

`BeginBlock` method was refactored to implement the `appmodule.HasBeginBlocker` interface.
```go
func (am AppModule) BeginBlock(goCtx context.Context) error {  // this now returns an error
	ctx := sdk.UnwrapSDKContext(goCtx)
	defer telemetry.ModuleMeasureSince(distrtypes.ModuleName, time.Now(), telemetry.MetricKeyBeginBlocker)

	// TODO this is Tendermint-dependent
	// ref https://github.com/cosmos/cosmos-sdk/issues/3095
	if ctx.BlockHeight() > 1 {
		return am.AllocateTokens(ctx)
	}

	return nil
}
```

`AllocateTokens` returns errors after refactoring it to match the cosmos-sdk/distribution `AllocateTokens`.

## Staking
Module now implements `appmodule.HasABCIGenesis` interface.

`InitGenesis` was refactored to implement the `appmodule.HasABCIGenesis` interface.
```diff
+ func (am AppModule) InitGenesis(ctx context.Context, cdc codec.JSONCodec, data json.RawMessage) []abci.ValidatorUpdate
- func (am AppModule) InitGenesis(ctx sdk.Context, cdc codec.JSONCodec, data json.RawMessage) []abci.ValidatorUpdate
```

`EndBlocker` was changed to `EndBlock` to support `module.HasABCIEndBlock` interface. Overriding `EndBlocker` and not `EndBlock` caused the validator changes to be propagated to comet by the staking module instead of the ccv-consumer module.

## Governance
Module now implements `appmodule.HasEndBlocker` interface.

`EndBlock` was refactored to implement `appmodule.HasEndBlocker` interface.
```diff
+ func (am AppModule) EndBlock(c context.Context) error
- func (am AppModule) EndBlock(ctx sdk.Context, request abci.RequestEndBlock) []abci.ValidatorUpdate
```

The inner workings of `EndBlock` were refactored to allow using the cosmos-sdk governance collection types instead of iterators (there no longer is a way to use raw iterators for iterating gov proposals).
```go
 func (am AppModule) EndBlock(c context.Context) error {
	ctx := sdk.UnwrapSDKContext(c)
	rng := collections.NewPrefixUntilPairRange[time.Time, uint64](ctx.BlockTime())
	keeper := am.keeper
	// if there are forbidden proposals in active proposals queue, refund deposit, delete votes for that proposal
	// and delete proposal from all storages
	err := am.keeper.ActiveProposalsQueue.Walk(ctx, rng, func(key collections.Pair[time.Time, uint64], _ uint64) (bool, error) {
		proposal, err := keeper.Proposals.Get(ctx, key.K2())
		if err != nil {
			return false, err
		}
		deleteForbiddenProposal(ctx, am, proposal)
		return false, nil
	})

	if err != nil {
		return err
	}
	return am.AppModule.EndBlock(ctx)
}
```

## App wiring & tests

Whitelisted proposal list was changed because `param-change` proposals were deprecated for most modules (they cannot be submitted).

Added to whitelists:
* `/cosmos.gov.v1beta1.TextProposal`


e2e tests were refactored to send the `TextProposal` instead of a `param-change` because there are no modules that can process `param-change` so we cannot use those proposals any longer.

