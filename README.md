# Interchain Security

[![Go Report Card](https://goreportcard.com/badge/github.com/cosmos/interchain-security)](https://goreportcard.com/report/github.com/cosmos/interchain-security)
[![Security Rating](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=security_rating)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Vulnerabilities](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=vulnerabilities)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Bugs](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=bugs)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Lines of Code](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=ncloc)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)
[![Coverage](https://sonarcloud.io/api/project_badges/measure?project=cosmos_interchain-security&metric=coverage)](https://sonarcloud.io/summary/new_code?id=cosmos_interchain-security)

**interchain-security** houses the code for implementing Interchain Security. The repo is currently a WIP and targetting v1 of Interchain Security. For more details on the Interchain Security protocol, take a look at the [specification](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/README.md).

CCV stands for cross chain validation and refers to the subset of Interchain Security related to the staking and slashing communication between the provider and consumer blockchains. The provider blockchain communicates staking changes to consumer blockchain(s), while the consumer blockchain may communicate slashing evidence to the provider blockchain.

The code for CCV is housed under [x/ccv](./x/ccv). The `types` folder contains types and related functions that are used by both provider and consumer chains, while the `consumer` module contains the code run by consumer chains and the `provider` module contains the code run by provider chain.

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

## Testing

See [testing docs](./docs/testing.md).

## Learn more

- [IBC Docs](https://docs.cosmos.network/master/ibc/)
- [IBC Protocol](https://ibcprotocol.org/)
- [IBC Specs](https://github.com/cosmos/ibc)
- [Cosmos SDK documentation](https://docs.cosmos.network)
- [Cosmos SDK Tutorials](https://tutorials.cosmos.network)
- [Discord](https://discord.gg/cosmosnetwork)
