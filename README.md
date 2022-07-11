# Interchain Security

[![Go Report Card](https://goreportcard.com/badge/github.com/cosmos/interchain-security)](https://goreportcard.com/report/github.com/cosmos/interchain-security)
[![Security Rating](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=security_rating)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Vulnerabilities](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=vulnerabilities)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Bugs](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=bugs)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Lines of Code](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=ncloc)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Coverage](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=coverage)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)

**interchain-security** houses the code for implementing Interchain Security (for more details, take a look at this [blog post](https://blog.cosmos.network/interchain-security-is-coming-to-the-cosmos-hub-f144c45fb035)). The repo is currently a WIP and targetting v1 of Interchain Security.

CCV stands for cross chain validation and refers to the subset of Interchain Security related to the staking and slashing communication between the provider and consumer blockchains. The provider blockchain communicates staking changes to consumer blockchain(s), while the consumer blockchain may communicate slashing evidence to the provider blockchain.

The code for CCV is housed under [x/ccv](./x/ccv). The `types` folder contains types and related functions that are used by both provider and consumer chains, while the `consumer` module contains the code run by consumer chains and the `provider` module contains the code run by provider chain.

NOTE: At the moment the testing app may not be functional, please rely on the IBC testing suite to write unit tests for the moment.

=======
## Instructions

**Prerequisites**

```bash
## For OSX or Linux

# go 1.18 (https://formulae.brew.sh/formula/go)
brew install go@1.18
# jq (optional, for testnet) (https://formulae.brew.sh/formula/jq)
brew install jq
# docker (optional, for integration tests, testnet) (https://docs.docker.com/get-docker/)

```

**Installing and running binaries**

```bash
# install interchain-security-pd and interchain-security-cd binaries
make install
# run provider
interchain-security-pd
# run consumer
interchain-security-cd
# (if the above fail, ensure ~/go/bin on $PATH)
export PATH=$PATH:$(go env GOPATH)/bin
```

Inspect the [Makefile](./Makefile) if curious.

**Running tests**

```bash
# run all unit tests using make
make test
# run all unit tests using go
go test ./...
# run all unit tests with verbose output
go test -v ./..
# run all unit tests with coverage stats
go test -cover ./..
# run a single unit test
go test -run <test-suite-name>/<test-name> ./...
# example: run a single unit test
go test -run TestProviderTestSuite/TestPacketRoundtrip ./...
# run the integration tests
go run ./integration-tests/...
# run golang native fuzz tests (https://go.dev/doc/tutorial/fuzz)
go test -fuzz=<regex-to-match-test-name>
```

**Linters and static analysis**

Several analyzers are used on the code including [CodeQL](https://codeql.github.com/), [SonarCloud](https://sonarcloud.io/), [golangci-lint](https://golangci-lint.run/) and [gosec](https://github.com/securego/gosec). Some of these are run on github when committing to PRs ect, but some tools are also applicable locally, and are built into golang.

```bash
# gofmt to format and simplify code (https://pkg.go.dev/cmd/gofmt)
gofmt -w -s -e .
# go vet to search for suspicious code (https://pkg.go.dev/cmd/vet)
go vet ./...
```

Some useful tools are included in the repository using [pre-commit](https://pre-commit.com/hooks.html). pre-commit lets you run developer tools either on every git commit, or manually with `pre-commit run --all-files`. See the [config](./.pre-commit-config.yaml) for details. In this repo the hooks are not installed to git, as that can be cumbersome, but it is still possible to benefit from them.

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

**Debugging**

If using VSCode, see [vscode-go/wiki/debugging](https://github.com/golang/vscode-go/wiki/debugging) to debug unit tests or go binaries.

**More**

More instructions will be added soon, in time for the testnet.

## Learn more

- [IBC Docs](https://docs.cosmos.network/master/ibc/)
- [IBC Protocol](https://ibcprotocol.org/)
- [IBC Specs](https://github.com/cosmos/ibc)
- [Cosmos SDK documentation](https://docs.cosmos.network)
- [Cosmos SDK Tutorials](https://tutorials.cosmos.network)
- [Discord](https://discord.gg/cosmosnetwork)
