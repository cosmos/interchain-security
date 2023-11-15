# Testing 

To increase confidence in the correctness of the Interchain Security code we consider various testing approaches.

## Unit Tests

Unit tests are useful for simple standalone functionality, CRUD operations, and asserting behavior at the lowest level. Unit tests should use golang's standard testing package, and be defined in files formatted as ```<file being tested>_test.go``` in the same directory as the file being tested, following standard conventions.

[Mocked external keepers](../../testutil/keeper/mocks.go) (implemented with [gomock](https://github.com/golang/mock)) are available for testing code that BRIEFLY interacts with external modules. Ie. do not use mocked external keepers to test the integration of the ccv module with external modules, or integration between consumer and provider.

Note if a test were to invoke more than 3-4 mock calls, it's likely not a true unit test.

### Note on Test Driven Development

When developing new features, it's important to implement logic in such a way that most functionality can be proved out with unit tests. Some tips to enact this are:

* Smaller funcs with targeted behavior and appropriate semantics
* Separating logic that interacts with external modules from logic that does not
* Designing funcs s.t. edge cases can be easily reasoned about

### Note on black box unit tests

Unit tests (and the funcs being tested) should be as small in scope as possible, for readability, and manageability.

If you're finding that a unit test needs callbacks, or specific setup to validate each test case, it's possible the func you're testing is not succinct enough.

### Note on mocking

To mock an interaction with external keepers, first confirm the method you're looking to mock is defined in [expected_keepers.go](../../x/ccv/types/expected_keepers.go). If needed, add the method signature to the appropriate keeper, and execute `make mocks`. This will generate mock code in [mocks.go](../../testutil/keeper/mocks.go).

Example mock usage in a unit test will be exemplified below:

```go
// Setup 
providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t)) 

// Tells the ctrl object to assert mock calls at the end of the func
defer ctrl.Finish()

// Specifies that we care about the order of mock calls, see also InAnyOrder
gomock.InOrder( 
    // Sets up a mock call to the external staking keeper's GetLastTotalPower method
    mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
        // Specifies the expected ctx object that'll be passed to the method,
        ctx,
        // Tells the mock framework to return a specific value. 
        ).Return(sdktypes.NewInt(500),
        // (optionally) specifies the method will be called twice.
        ).Times(2),

    // Sets up a mock call to the external client keeper's GetClientState method
    // This mock will needs to be executed AFTER the first call to GetLastTotalPower.
    mocks.MockClientKeeper.EXPECT().GetClientState(
        // Specifies the expected ctx object and string parameter that'll be passed to the method
        ctx, "clientIDToConsumer",
        // Returns a mock object of the expected type, and a boolean indicating success
        ).Return(&ibctmtypes.ClientState{ChainId: "consumerChainID"}, true,
    // Specifies the method can be called any number of times 
    ).AnyTimes(),
)

// Do whatever testing you want that calls the mocks 
providerKeeper.MethodThatCallsMocks()

```

## Integration Tests

[integration-tests](../../tests/integration/) utilize the [IBC Testing Package](https://github.com/cosmos/ibc-go/tree/main/testing), and test functionality that is wider in scope than a unit test, but still able to be validated in-memory. Ie. code where advancing blocks would be useful, simulated handshakes, simulated packet relays, etc.

In scenarios where one doesn't desire to test against a real system in docker, or validate CLI interactions, integration tests are quick the most useful. You can assert logic that spans multiple sdk modules, and multiple consumers connected to a provider.

To run integration tests against your own consumer/provider implementations, use [instance_test.go](../../tests/integration/instance_test.go) as an example. All you'll need to do is make sure your applications implement the necessary interfaces defined in [interfaces.go](../../testutil/integration/interfaces.go), pattern match [specific_setup.go](../../testutil/ibc_testing/specific_setup.go), then pass in the appropriate types and parameters to the suite, as is done in `instance_test.go` for the dummy provider/consumer implementations.

### Tips on working with integration tests and IBC-go testing

**Avoid context caching:** When passing a context obj to a keeper method, use `s.consumerCtx()` or `s.providerCtx()` appropriately inline, instead of caching a local context object for the entire integration test and passing that into keeper methods. Reasoning: in golang when you pass a variable to a function as an argument, a copy of the value is made, and changes to that copy within the function do not affect the original value outside of the function. Ie. any state mutations made by a keeper call can only be seen by fetching a new context object from the suite.

**Attempt to use the highest level IBC methods:** When writing a test that needs to relay packet(s) that're already committed, use `relayAllCommittedPackets()` in [common.go](../../tests/integration/common.go). Or if you need to manually commit/relay a custom packet, use `sendOnProviderRecvOnConsumer()` or `sendOnConsumerRecvOnProvider()`. Note each method has its own intricacies with how IBC state is mutated, and there's multiple ways to achieve the same result. The mentioned helper methods are what's most commonly used in this repo.

## Differential Tests (DEPRECATED)

[Differential tests](../../tests/difference/) are similar to integration tests, but they compare the system state to an expected state generated from a model implementation.

## End-to-End (E2E) Tests 

[E2E tests](../../tests/e2e/) run true consumer and provider chain binaries within a docker container and are relevant to the highest level of functionality. E2E tests use queries/transactions invoked from CLI to drive and validate the code.

## Running Tests
Tests can be run using `make`:

```bash
# run unit, integration, diff, and E2E tests
make test

# run unit and integration tests - prefer this for local development
make test-short

# run difference tests
make test-diff

# run E2E tests
make test-e2e

# equivalent to make test with caching disabled
make test-no-cache
```

Alternatively you can run tests using `go test`:
```bash
# run all unit, integration, and diff tests using go
go test ./...
# run all unit, integration, and diff tests with verbose output
go test -v ./..
# run all unit, integration, and diff tests with coverage stats
go test -coverpkg=./x/... -coverprofile=coverage.out ./...
# run a single unit test
go test -run <unit-test-name> path/to/package
# example: run a single unit test
go test -run TestSlashAcks ./x/ccv/provider/keeper
# run a single integration test
go test -run <test-suite-name>/<test-name> ./...
# example: run a single integration test
go test -run TestProviderTestSuite/TestPacketRoundtrip ./...
# run all E2E tests
go run ./tests/e2e/...
# run all E2E tests with a local cosmos sdk
go run ./tests/e2e/... --local-sdk-path "/Users/bob/Documents/cosmos-sdk/"
# run golang native fuzz tests (https://go.dev/doc/tutorial/fuzz)
go test -fuzz=<regex-to-match-test-name>
# run verbose E2E tests
go run ./tests/e2e/... --local-sdk-path "/Users/bob/Documents/cosmos-sdk/" --verbose
```

### Tesing with Gaia as the provider

Integration tests can be run with Gaia as the provider.
By default, the latest tagged release of Gaia is used - this includes release candidates and stabile releases.

```bash
# use gaia as the provider
go run ./tests/integration/... --use-gaia

# use gaia as the provider - use specific tagged release
go run ./tests/integration/... --use-gaia --gaia-tag v9.0.0
```

NOTE: versions < v9.0.0 are not compatible with ICS.

## Linters and Static Analysis

Several analyzers are used on the code including [CodeQL](https://codeql.github.com/), [SonarCloud](https://sonarcloud.io/), [golangci-lint](https://golangci-lint.run/) and [gosec](https://github.com/securego/gosec). Some of these are run on github when committing to PRs ect, but some tools are also applicable locally, and are built into golang.

```bash
# gofmt to format and simplify code (https://pkg.go.dev/cmd/gofmt)
gofmt -w -s -e .
# go vet to search for suspicious code (https://pkg.go.dev/cmd/vet)
go vet ./...
```

Some useful tools are included in the repository using [pre-commit](https://pre-commit.com/hooks.html). pre-commit lets you run developer tools either on every git commit, or manually with `pre-commit run --all-files`. See the [config](../../.pre-commit-config.yaml) for details. In this repo the hooks are not installed to git, as that can be cumbersome, but it is still possible to benefit from them.

```bash
## Prerequisites

# pre-commit
brew install pre-commit
# goimports (https://pkg.go.dev/golang.org/x/tools/cmd/goimports)
go install golang.org/x/tools/cmd/goimports@latest
# gocyclo (https://github.com/fzipp/gocyclo)
go install github.com/fzipp/gocyclo/cmd/gocyclo@latest
# go-critic https://github.com/go-critic/go-critic
go install github.com/go-critic/go-critic/cmd/gocritic@latest

## Run the tools

pre-commit run --all-files
```

## Debugging

If using VSCode, see [vscode-go/wiki/debugging](https://github.com/golang/vscode-go/wiki/debugging) to debug unit tests or go binaries.

## More

More instructions will be added soon, in time for the testnet. 