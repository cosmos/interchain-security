
# Integration Testing

Integration tests are categorized into files as follows:

- `setup.go` - setup for the integration tests
- `common.go` - helper functions
- `valset_update.go` - integration tests for the _Validator Set Update_ sub-protocol
- `unbonding.go` - integration tests for the _Completion of Unbonding Operations_
- `slashing.go` - integration tests for the _Consumer Initiated Slashing_ sub-protocol
- `distribution.go` - integration tests for the _Reward Distribution_ sub-protocol
- `stop_consumer.go` - integration tests for the _Consumer Chain Removal_ sub-protocol
- `normal_operations.go` - integration tests for _normal operations_ of ICS enabled chains
- `query_providerinfo_test.go` - integration tests for the `GetProviderInfo` method
- `changeover.go` - integration tests for reuse of existing transfer channels
- `double_vote.go` - integration tests for the handling of double voting
- `misbehavior.go` - integration tests for the handling of misbehaviors
- `partial_set_security_test.go` - integration tests for the partial set security
- `expired_client.go` - integration tests for expired clients
- `key_assignment.go` - integration tests for key assignment
- `instance_test.go` - ties the integration test structure into golang's standard test mechanism, with appropriate definitions for concrete app types and setup callback

To run the integration tests defined in this repo on any arbitrary consumer and provider implementation, copy the pattern exemplified in `instance_test.go` and `specific_setup.go`
