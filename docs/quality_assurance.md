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

> TODO decide what should be covered by the audit and the priority

## Software Engineering

| Concern | Code Review | Automatic Tools | Unit Testing |
| ------- | ----------- | --------------- | ------------ |
| Unexpected panics | `TODO` | `??` | `??` |
| Handling errors | `TODO` | `??` | `??` |
| Accessing state (setters, getters, iterators) | `TODO` | `??` | `Low coverage` |
| Serialization / deserialization | `TODO` | `??` | `??` |

## Integration with IBC

Interchain Security is an IBC application and, thus, it relies on IBC to establish a separate channel between the provider chain and every consumer chain. Interchain Security relies on the IBC v3.0 golang [implementation](https://github.com/cosmos/ibc-go/tree/v3.0.0).

IBC packets:
- ValidatorSetChangePacket
- MaturedVSCPacket
- SlashPacketData

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Create IBC clients | `TODO` (ibc-go team) | `Done` | `??` | `TODO` | `NA` |
| Getting consumer `UnbondingPeriod` from IBC client | `TODO` (ibc-go team) | `??` | `??` | `TODO` | `NA` |
| Create CCV channel (handshake) | `TODO` (ibc-go team) | `Done` | `??` | `TODO` | `TODO` |
| Sending IBC packets <br /> - see `x/ccv/utils/utils.go:SendIBCPacket()` | `TODO` (ibc-go team) | `Done` | `??` | `TODO` | `NA` |
| Handling acknowledgments | `TODO` (ibc-go team) | `Low coverage` | `??` | `TODO` | `NA` |
| Handling timeouts | `TODO` (ibc-go team) | `Low coverage` | `??` | `TODO` | `NA` |
| Handling IBC client expiration | `TODO` (ibc-go team) | `??` | `??` | `TODO` | `NA` |
| ICS-20 channel creation | `TODO` (ibc-go team) | `??` | `??` | `TODO` | `NA` |
| ICS-20 transfer | `TODO` (ibc-go team) | `??` | `??` | `TODO` | `NA` |

## Integration with Cosmos SDK

A prerequisite of the code review is to open a PR with all the [SDK changes](https://github.com/cosmos/cosmos-sdk/tree/interchain-security-rebase) needed by Interchain Security.

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Changes to staking module | `TODO` (sdk team) | `Low coverage` | `??` | `TODO` | `NA` |
| Changes to slashing module | `TODO` (sdk team) | `??` | `??` | `TODO` | `NA` |
| Changes to evidence module | `TODO` (sdk team) | `??` | `??` | `TODO` | `NA` |

## Provider Chain Correctness

The main concern addressed in this section is the correctness of the provider chain (e.g., the Cosmos Hub). In other words, when Interchain Security is enabled (i.e., the provider CCV module is enabled), the safety and liveness properties still hold. This _**MUST**_ be the case regardless of the number of consumer chains (i.e., none, one, or multiple consumer chains).

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Liveness of undelegations (eventual completion) | `TODO` | `Done` | `??` | `TODO` | `TODO` |
| Liveness of redelegations | `TODO` | `TODO` | `??` | `TODO` | `TODO` |
| Liveness of validator unbondings | `TODO` | `TODO` | `??` | `TODO` | `TODO` |
| A validator cannot get slashed more than once for double signing, regardless of how many times it double signs on different chains (consumers or provider) | `TODO` | `??` | `??` | `TODO` | `TODO` |
| A validator cannot get slashed multiple times for downtime on the same chain without requesting to `Unjail` itself in between | `TODO` | `??` | `??` | `TODO` | `TODO` |
| A validator can be slashed multiple times for downtime on different chains | `TODO` | `??` | `??` | `TODO` | `TODO` |

> TODO create clear concerns re. these other actions that may affect the provider chain:
> - Handling proposals
>   - `SpawnConsumerChainProposal`
>   - `StopConsumerChainProposal`
> - Create consumer chains
> - Remove consumer chains
> - Restart provider chain with IS enabled

## Interchain Security Protocol Correctness

The main concern addressed in this section is the correctness of the Interchain Security protocol. In other words, the implementation should be aligned with the Interchain Security [specification](https://github.com/cosmos/ibc/blob/master/spec/appics-028-cross-chain-validation/README.md). 

This requires the implementation to guarantee the following system properties (see the specification for details):
- Bond-Based Consumer Voting Power
- Slashable Consumer Misbehavior
- Consumer Rewards Distribution

> TODO create clear concerns from the above properties

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |


## Consumer Chain Correctness

The main concern addressed in this section is the correctness of the consumer chains. In other words, when Interchain Security is enabled (i.e., the consumer CCV module is enabled), the safety and liveness properties still hold. This also covers various flavor of consumer chains:
- minimum viable consumer chain ([mvcc](https://github.com/cosmos/interchain-security/issues/139))
- governance-enabled consumer chain ([gov-cc](https://github.com/cosmos/interchain-security/issues/141)), with the modified staking and distribution modules (see `x/ccv/staking` and `x/ccv/distribution`); also, must look at the [atom-gov module](https://github.com/cosmos/interchain-security/issues/162)
- CosmWasm-enabled consumer chain ([wasm-cc](https://github.com/cosmos/interchain-security/issues/143)), with the CosmWasm module enabled

> TODO create clear concerns for `gov-cc` and `wasm-cc` once the implementations are done

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Consumer chain liveness (blocks are being produced) | `TODO` | `NA` | `??` | `TODO` | `NA` |
| Every validator set on any consumer chain MUST either be or have been a validator set on the provider chain. | `TODO` | `NA` | `??` | `TODO` | `TODO` |
| A chain has the ability to restart as a consumer chain with no more than 24 hours downtime | `TODO` | `NA` | `??` | `TODO` | `NA` |
| Governance on `gov-cc` | `TODO` | `??` | `??` | `TODO` | `NA` |
| CosmWasm on `wasm-cc` | `TODO` | `??` | `??` | `TODO` | `NA` |

> TODO Scenarios to consider for restarting chains, client expiration
>   - A consumer chain restarts as a normal chain (after shutting down, either controlled or due to timing out)
>   - A consumer chain restarts as a consumer chain (after shutting down, either controlled or due to timing out)