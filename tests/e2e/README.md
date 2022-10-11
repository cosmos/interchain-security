## End To End Testing

## TODO documentation here

E2e tests are categorized into files as follows:

- `setup_test.go` - setup for the e2e tests
- `common_test.go` - helper functions
- `channel_init_test.go` - e2e tests for the _Channel Initialization_ sub-protocol
- `valset_update_test.go` - e2e tests for the _Validator Set Update_ sub-protocol
- `unbonding_test.go` - e2e tests for the _Completion of Unbonding Operations_
- `slashing_test.go` - e2e tests for the _Consumer Initiated Slashing_ sub-protocol
- `distribution_test.go` - e2e tests for the _Reward Distribution_ sub-protocol
- `stop_consumer_test.go` - e2e tests for the _Consumer Chain Removal_ sub-protocol
- `normal_operations_test.go` - e2e tests for _normal operations_ of ICS enabled chains 