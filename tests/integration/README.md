
# End To End Testing

Intg tests are categorized into files as follows:

- `setup.go` - setup for the integration tests
- `common.go` - helper functions
- `channel_init.go` - integration tests for the _Channel Initialization_ sub-protocol
- `valset_update.go` - integration tests for the _Validator Set Update_ sub-protocol
- `unbonding.go` - integration tests for the _Completion of Unbonding Operations_
- `slashing.go` - integration tests for the _Consumer Initiated Slashing_ sub-protocol
- `distribution.go` - integration tests for the _Reward Distribution_ sub-protocol
- `stop_consumer.go` - integration tests for the _Consumer Chain Removal_ sub-protocol
- `normal_operations.go` - integration tests for _normal operations_ of ICS enabled chains
- `expired_client.go` - integration tests for testing expired clients
- `key_assignment.go` - integration tests for testing key assignment
- `instance_test.go` - ties the integration test structure into golang's standard test mechanism, with appropriate definitions for concrete app types and setup callback

To run the integration tests defined in this repo on any arbitrary consumer and provider implementation, copy the pattern exemplified in `instance_test.go` and `specific_setup.go`
