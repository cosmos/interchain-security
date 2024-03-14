# import change only [file list]
* app/consumer-democracy/ante_handler.go
* app/consumer-democracy/proposals_whitelisting.go
* app/consumer-democracy/proposals_whitelisting_test.go
* app/consumer/ante/disabled_modules_ante_test.go
* app/consumer/ante/msg_filter_ante_test.go
* app/consumer/ante_handler.go
* app/provider/ante_handler.go
* app/sovereign/ante_handler.go
* cmd/interchain-security-cdd/cmd/root.go

## tests

### Integration
* tests/integration/changeover.go


### E2E
* tests/e2e/trace_handlers_test.go
* tests/e2e/json_marshal_test.go
* tests/e2e/state_rapid_test.go
* tests/e2e/steps_consumer_misbehaviour.go

### Util
* testutil/crypto/evidence.go
* testutil/simibc/ordered_outbox.go
* testutil/simibc/relayed_path.go


### Modules
* x/ccv/consumer/ibc_module.go
* x/ccv/consumer/ibc_module_test.go
* x/ccv/consumer/keeper/genesis_test.go
* x/ccv/consumer/keeper/provider_info.go
* x/ccv/consumer/keeper/relay.go
* x/ccv/consumer/keeper/soft_opt_out_test.go [seems long but it's just imports and name updates]
* x/ccv/consumer/types/genesis.go
* x/ccv/consumer/types/genesis_test.go


* x/ccv/provider/ibc_module.go
* x/ccv/provider/ibc_module_test.go
* x/ccv/provider/types/genesis.go
* x/ccv/provider/types/legacy_proposal_test.go [rename from proposal_test.go and update imports]
* x/ccv/types/genesis.go
* x/ccv/types/params.go
* x/ccv/types/shared_params.go
* x/ccv/types/utils.go
* x/ccv/types/utils_test.go


# Additions
# Sovereign/Standalone chain

Standalone simapp is modeled after the `app/consumer/app.go`. It must support all features that `app/consumer/app.go` supports so we can use it in standalone to consumer changeover procedures in our test suites.

