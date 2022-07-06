# Interchain Security

[![Go Report Card](https://goreportcard.com/badge/github.com/cosmos/interchain-security)](https://goreportcard.com/report/github.com/cosmos/interchain-security)
[![Security Rating](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=security_rating)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Vulnerabilities](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=vulnerabilities)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Bugs](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=bugs)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Lines of Code](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=ncloc)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)

**interchain-security** houses the code for implementing Interchain Security: <https://blog.cosmos.network/interchain-security-is-coming-to-the-cosmos-hub-f144c45fb035>. The repo is currently a WIP and targetting v1 of Interchain Security.

CCV stands for cross chain validation and refers to the subset of Interchain Security related to the staking and slashing communication between the provider and consumer blockchains. The provider blockchain communicates staking changes to consumer blockchain(s), while the consumer blockchain may communicate slashing evidence to the provider blockchain.

The code for CCV is housed under [x/ccv](./x/ccv). The `types` folder contains types and related functions that are used by both provider and consumer chains, while the `consumer` module contains the code run by consumer chains and the `provider` module contains the code run by provider chain.

NOTE: At the moment the testing app may not be functional, please rely on the IBC testing suite to write unit tests for the moment.

**Linters and static analysis**

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

## Learn more

- [IBC Docs](https://docs.cosmos.network/master/ibc/)
- [IBC Protocol](https://ibcprotocol.org/)
- [IBC Specs](https://github.com/cosmos/ibc)
- [Cosmos SDK documentation](https://docs.cosmos.network)
- [Cosmos SDK Tutorials](https://tutorials.cosmos.network)
- [Discord](https://discord.gg/cosmosnetwork)
