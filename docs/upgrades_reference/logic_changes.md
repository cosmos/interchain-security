# logic changes [file list]
Order of changes:
1. x/
2. app -> integration test setup requires a working app
3. tests/integration & mbt
4. tests/e2e

* app/consumer-democracy/abci.go
* app/consumer-democracy/export.go
* app/consumer/abci.go [important]
* app/consumer/export.go
* app/params/proto.go [important]
* app/provider/abci.go [important]
* app/provider/export.go [important]
* app/sovereign/abci.go [important]
* app/sovereign/export.go [important]
* cmd/interchain-security-cd/cmd/root.go [important; app setup]
* cmd/interchain-security-pd/cmd/root.go


# test changes
* app/consumer-democracy/ante/forbidden_proposals_ante_test.go
* tests/e2e/actions.go
* tests/e2e/config.go [add expedited period]

* tests/e2e/state.go [important; changes marshalling]
* tests/e2e/state_rapid_test.go
* tests/e2e/steps.go

### [proposal voting changed -> must provide numeric]
* tests/e2e/steps_democracy.go
* tests/e2e/steps_reward_denom.go
* tests/e2e/steps_sovereign_changeover.go
* tests/e2e/steps_start_chains.go
* tests/e2e/steps_stop_chain.go

## Update e2e scripts
[must provide `q block --height 0` to force fetching current block]
* tests/e2e/testnet-scripts/start-chain.sh 
* tests/e2e/testnet-scripts/start-changeover.sh
* tests/e2e/testnet-scripts/start-sovereign.sh

## Update integration test setup
* tests/integration/common.go
* tests/integration/setup.go [updates to packet listening and initialization due to interface changes]

## update assertions (change types etc)
* tests/integration/democracy.go
* tests/integration/distribution.go
* tests/integration/double_vote.go
* tests/integration/expired_client.go
* tests/integration/key_assignment.go
* tests/integration/misbehaviour.go
* tests/integration/normal_operations.go
* tests/integration/slashing.go
* tests/integration/stop_consumer.go
* tests/integration/unbonding.go
* tests/integration/valset_update.go

MBT Driver
* tests/mbt/driver/common.go
* tests/mbt/driver/core.go
* tests/mbt/driver/mbt_test.go
* tests/mbt/driver/setup.go


Not sure needed?
* tests/integration/throttle.go
* tests/integration/throttle_retry.go

Utils
* testutil/crypto/crypto.go [imports, fetching info]
* testutil/crypto/evidence.go [imports, fetching info]
    * MakeVote() interface has changed

* testutil/ibc_testing/generic_setup.go [init & proposal updates]
* testutil/ibc_testing/specific_setup.go [init & proposal updates]
-> interfaces
* testutil/integration/interfaces.go [support updated interfaces and enforce them]
* testutil/keeper/expectations.go [support updated interfaces and enforce them]
* testutil/keeper/mocks.go [run `make mocks` after updating expectations by hand and expected keepers] 
* testutil/keeper/unit_test_helpers.go [imports & setup]
* testutil/simibc/chain_util.go [imports & setup]
    * use `FinalizeBlock` and update parsing
* testutil/simibc/relay_util.go

## Expected keepers
* x/ccv/types/expected_keepers.go [affects mocks and all tests] +


## Modules (mostly adapting to new interfaces, checking errs and updating names)

### Consumer
* x/ccv/consumer/keeper/changeover.go
* x/ccv/consumer/keeper/changeover_test.go
* x/ccv/consumer/keeper/distribution.go
* x/ccv/consumer/keeper/distribution_test.go
* x/ccv/consumer/keeper/hooks.go

* x/ccv/consumer/keeper/keeper.go
* update `iterator` initialization
```diff
- iterator := sdk.KVStorePrefixIterator(store, []byte{types.PacketMaturityTimeBytePrefix})
+ iterator := storetypes.KVStorePrefixIterator(store, []byte{types.PacketMaturityTimeBytePrefix})
```
* `func (k Keeper) GetLastStandaloneValidators(ctx sdk.Context)` now returns a value and err


* x/ccv/consumer/keeper/keeper_test.go
* x/ccv/consumer/keeper/legacy_params.go [addition]
* x/ccv/consumer/keeper/migration.go
* x/ccv/consumer/keeper/migration_test.go
* x/ccv/consumer/keeper/params.go
* x/ccv/consumer/keeper/relay_test.go

* x/ccv/consumer/keeper/soft_opt_out_test.go
* x/ccv/consumer/keeper/soft_opt_out.go
* interfaces changed `UpdateSlashingSigningInfo`

* x/ccv/consumer/keeper/validators.go [!important]
* changed all staking interface methods to match cosmos-sdk v50
* some methods return errs so handling was added

* x/ccv/consumer/keeper/validators_test.go [imports, err checks, extra assertions]
* x/ccv/consumer/module.go [important!]

* x/ccv/consumer/types/keys.go [important! params key added to store]
* x/ccv/consumer/types/keys_test.go


## Democracy
* x/ccv/democracy/distribution/module.go [important]
* refactor `AllocateTokens`
    * adds panics in multiple places due to err handling

* x/ccv/democracy/governance/module.go [important]
* x/ccv/democracy/staking/module.go [important]

## Provider
* x/ccv/provider/client/cli/query.go [add params query]
* x/ccv/provider/client/cli/query.go [imports, signer field in NewAssignConsumerKeyCmd]
* x/ccv/provider/client/legacy_proposal_handler.go [rename proposal_handler.go - deprecated]
* x/ccv/provider/client/legacy_proposals.go [added but deprecated]
* x/ccv/provider/handler.go [imports]
* x/ccv/provider/handler_test.go



[sensitive]
* x/ccv/provider/keeper/consumer_equivocation.go [tricky - changes to cometBFT sign.Absent() flags => sign.Absent() changed to comparison sign.BlockIDFlag == tmtypes.BlockIDFlagAbsent]
* added error checks in `JailAndTombstoneValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress)`
* added err checks in `SlashValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress)`



* x/ccv/provider/keeper/consumer_equivocation_test.go


-> check that endblock returns correct errors
* x/ccv/provider/module.go [important]
* x/ccv/provider/module_test.go


* x/ccv/provider/types/codec.go [double check RegisterLegacyAminoCodec and RegisterInterfaces]
* x/ccv/provider/types/keys.go [adds parameters bytekey -> make sure you don't override it!!]
* x/ccv/provider/types/keys_test.go
* x/ccv/provider/types/legacy_proposal.go [rename from proposal.go, update logic]
* x/ccv/provider/types/legacy_proposal_test.go [check some weird comments about comparisons]
* x/ccv/provider/types/msg.go [new message type]
* x/ccv/provider/types/params.go
* x/ccv/provider/types/params_test.go


#### Change to store access
```
// changes store module imports and iterator initialization

- iterator := sdk.KVStorePrefixIterator(store, []byte{types.ConsumerRewardDenomsBytePrefix})
+ iterator := storetypes.KVStorePrefixIterator(store, []byte{types.ConsumerRewardDenomsBytePrefix})
```

* x/ccv/provider/keeper/distribution.go
* update iterator


* x/ccv/provider/keeper/keeper_test.go
* x/ccv/provider/keeper/keeper.go
* updated `NewKeeper` and the `types Keeper struct` with v50 types (authority, storeKey, storeService, validatorAddressCodec, consensusAddressCodec)
* rm `SetParamSpace [DEPRECATED]`
* use v50 logger
* update all iterators:
```go
- iterator := sdk.KVStorePrefixIterator(store, []byte{types.ProposedConsumerChainByteKey})
+ iterator := storetypes.KVStorePrefixIterator(store, []byte{types.ProposedConsumerChainByteKey})
```


* x/ccv/provider/keeper/key_assignment.go [ also logic changes regarding key assignment and validator access ]
```go
- iterator := sdk.KVStorePrefixIterator(store, prefix)
+ iterator := storetypes.KVStorePrefixIterator(store, prefix)
```

Updates changing the logic slightly:
```go
func (k Keeper) AssignConsumerKey(
	ctx sdk.Context,
	chainID string,
	validator stakingtypes.Validator,
	consumerKey tmprotocrypto.PublicKey,
) error
```

```go
func (k Keeper) ValidatorConsensusKeyInUse(ctx sdk.Context, valAddr sdk.ValAddress) bool
```


* x/ccv/provider/keeper/key_assignment_test.go -> partial


#### Other changes
* x/ccv/provider/keeper/genesis_test.go
* x/ccv/provider/keeper/grpc_query.go [adds params query]

* x/ccv/provider/keeper/hooks.go
* update all methods to use `context.Context` instead of `sdk.Context`
* double check returned values in `func (h Hooks) GetConsumerAdditionLegacyPropFromProp`

* x/ccv/provider/keeper/hooks_test.go
* x/ccv/provider/keeper/legacy_params.go

* x/ccv/provider/keeper/migration_test.go
* x/ccv/provider/keeper/migration.go
    * was re-done

* x/ccv/provider/keeper/msg_server.go

* x/ccv/provider/keeper/params_test.go
* x/ccv/provider/keeper/params.go
* migrated params to the new interface and update all getters
* added legacy params file for accessing deprecated params subspace

* x/ccv/provider/keeper/proposal_test.go
* x/ccv/provider/keeper/proposal.go
* prefixed deprecated handlers with `Legacy`
* updated `MakeConsumerGenesis`: added err checks
* moved deprecated handlers to `legacy_proposal.go`


* x/ccv/provider/keeper/relay_test.go -> generate after updating mocks
* x/ccv/provider/keeper/relay.go
* updated err handling to support new interfaces
    * `completeMaturedUnbondingOps(ctx sdk.Context)`


* x/ccv/provider/keeper/throttle_test.go
* x/ccv/provider/keeper/throttle.go
* update err handling
* left myself a note: `@MSalopek double check this conversion and see if it's necessary`


* x/ccv/provider/proposal_handler.go
* x/ccv/provider/proposal_handler_test.go
* x/ccv/provider/types/codec.go
* x/ccv/provider/types/errors.go
* x/ccv/provider/types/genesis.go


































# less important
* cmd/interchain-security-cd/main.go
* cmd/interchain-security-cdd/main.go
* cmd/interchain-security-pd/main.go
* cmd/interchain-security-sd/main.go