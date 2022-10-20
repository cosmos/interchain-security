
# End To End Testing

E2e tests are categorized into files as follows:

- `setup.go` - setup for the e2e tests
- `common.go` - helper functions
- `channel_init.go` - e2e tests for the _Channel Initialization_ sub-protocol
- `valset_update.go` - e2e tests for the _Validator Set Update_ sub-protocol
- `unbonding.go` - e2e tests for the _Completion of Unbonding Operations_
- `slashing.go` - e2e tests for the _Consumer Initiated Slashing_ sub-protocol
- `distribution.go` - e2e tests for the _Reward Distribution_ sub-protocol
- `stop_consumer.go` - e2e tests for the _Consumer Chain Removal_ sub-protocol
- `normal_operations.go` - e2e tests for _normal operations_ of ICS enabled chains
- `instance_test.go` - ties the e2e test structure into golang's standard test mechanism, with appropriate definitions for concrete app types and setup callback

To run the e2e tests defined in this repo on any arbitrary consumer and provider implementation, copy the pattern exemplified in `instance_test.go`
