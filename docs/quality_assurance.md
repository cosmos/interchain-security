# Interchain Security: Quality Assurance

This document contains the overview of the quality assurance process necessary for the release of Interchain Security v1. 

The verification of Interchain Security is done using the following approaches:
- code review
- automatic software engineering tools (e.g., SonarCloud, gosec)
- unit testing
- differential testing
- incentivized testnet
- audit (with the Apalache team from Informal Systems)

The verification of Interchain Security is split across the following concerns:
- Correct software engineering practices (e.g., error handling, serialization, deserialization).
- The correct integration with IBC (i.e., [ibc-go](https://github.com/cosmos/ibc-go/tree/v3.0.0)).
- The correct integration with Cosmos SDK (i.e., [cosmos-sdk](https://github.com/cosmos/cosmos-sdk/tree/v0.45.6)).
- The correctness of the provider chain, i.e., the provider CCV module does not break the liveness or the safety of the provider chain. 
- The correctness of the Interchain Security protocol, i.e., the protocol follows the [specification](https://github.com/cosmos/ibc/blob/master/spec/appics-028-cross-chain-validation/README.md).
- The correctness of the consumer chain, i.e., both liveness or safety hold.

## Software Engineering

| Concern | Code Review | Automatic Tools | Unit Testing |
| ------- | ----------- | --------------- | ------------ |
| Unexpected panics | `TODO` | `??` | `??` |
| Handling errors | `TODO` | `??` | `??` |
| Accessing state (setters, getters, iterators) | `TODO` | `??` | `Low coverage` |
| Serialization / deserialization | `TODO` | `??` | `??` |

> @danwt @sainoe Is there something else that we should check for? 

## Integration with IBC

Interchain Security is an IBC application and, thus, it relies on IBC to establish a separate channel between the provider chain and every consumer chain. Interchain Security relies on the IBC v3.0 golang [implementation](https://github.com/cosmos/ibc-go/tree/v3.0.0).

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Create IBC clients | `TODO` (ibc-go team) | `Done` | `??` | `TODO` | `NA` |
| Getting consumer `UnbondingPeriod` from IBC client | `TODO` (ibc-go team) | `??` | `??` | `TODO` | `NA` |
| Create CCV channel (handshake) | `TODO` (ibc-go team) | `Done` | `??` | `TODO` | `TODO` |
| Sending IBC packets | `TODO` (ibc-go team) | `Done` | `??` | `TODO` | `NA` |
| Handling acknowledgments | `TODO` (ibc-go team) | `Low coverage` | `??` | `TODO` | `NA` |
| Handling timeouts | `TODO` (ibc-go team) | `Low coverage` | `??` | `TODO` | `NA` |
| Handling IBC client expiration | `TODO` (ibc-go team) | `??` | `??` | `TODO` | `NA` |

> @AdityaSripal Is there something else that we should check for? 

## Integration with Cosmos SDK

A prerequisite of the code review is to open a PR with all the [SDK changes](https://github.com/cosmos/cosmos-sdk/tree/interchain-security-rebase) needed by Interchain Security.

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Changes to staking module | `TODO` (sdk team) | `Low coverage` | `??` | `TODO` | `NA` |
| Changes to slashing module | `TODO` (sdk team) | `??` | `??` | `TODO` | `NA` |
| Changes to evidence module | `TODO` (sdk team) | `??` | `??` | `TODO` | `NA` |

> @sainoe Is there something else that we should check for? 

## Provider Chain Correctness

## Interchain Security Protocol Correctness

## Consumer Chain Correctness