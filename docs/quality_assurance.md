# Interchain Security: Quality Assurance

This document contains the overview of the quality assurance process necessary for the release of Interchain Security v1. 

The verification of Interchain Security is done using the following approaches:
- code review
- automatic software engineering tools (e.g., SonarCloud, gosec)
- unit testing
- differential testing using heuristics
- incentivized testnet
- protocol audit (with the Apalache team from Informal Systems)

The verification of Interchain Security is split across the following concerns:
- Correct software engineering (e.g., error handling, serialization, deserialization).
- The correct integration with IBC (i.e., [ibc-go](https://github.com/cosmos/ibc-go/tree/v3.0.0)).
- The correct integration with Cosmos SDK (i.e., [cosmos-sdk](https://github.com/cosmos/cosmos-sdk/tree/v0.45.6)).
- The correctness of the provider chain, i.e., the provider CCV module does not break the liveness or the safety of the provider chain. 
- The correctness of the Interchain Security protocol, i.e., the protocol follows the [specification](https://github.com/cosmos/ibc/blob/master/spec/appics-028-cross-chain-validation/README.md).
- The correctness of the consumer chain, i.e., both liveness or safety hold.

> TODO decide what should be covered by the protocol audit and the priority

## Software Engineering

| Concern | Code Review | Automatic Tools | Unit Testing |
| ------- | ----------- | --------------- | ------------ |
| Unexpected panics | `Scheduled` | `??` | `??` |
| Handling errors | `Scheduled` | `gosec` | `??` |
| Accessing store (setters, getters, iterators) | `Scheduled` | `??` | `Partial coverage` |
| Serialization / deserialization | `Scheduled` | `??` | `??` |
| Storage leaks | `Scheduled` | `NA` | `??` |

## Integration with IBC

Interchain Security is an IBC application and, thus, it relies on IBC to establish a separate channel between the provider chain and every consumer chain. Interchain Security relies on the IBC v3.0 golang [implementation](https://github.com/cosmos/ibc-go/tree/v3.0.0).

IBC packets:
- ValidatorSetChangePacket
- MaturedVSCPacket
- SlashPacketData

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Create IBC clients | `Scheduled` (ibc-go team) | `Done` | `Future work` | `Scheduled` | `NA` |
| Getting consumer `UnbondingPeriod` from IBC client | `Scheduled` (ibc-go team) | `??` | `NA` | `NA` | `NA` |
| Create CCV channel (handshake) | `Scheduled` (ibc-go team) | `Done` | `Future work` | `Scheduled` | `Scheduled` |
| Sending IBC packets <br /> - see `x/ccv/utils/utils.go:SendIBCPacket()` | `Scheduled` (ibc-go team) | `Done` | `Done` | `Scheduled` | `NA` |
| Handling acknowledgments | `Scheduled` (ibc-go team) | `Partial coverage` | `Scheduled` | `Scheduled` | `NA` |
| Handling timeouts | `Scheduled` (ibc-go team) | `Partial coverage` | `Future work` | `Scheduled` | `NA` |
| Handling IBC client expiration | `Scheduled` (ibc-go team) | `??` | `Future work` | `Scheduled` | `NA` |
| ICS-20 channel creation | `Scheduled` (ibc-go team) | `??` | `Future work` | `Scheduled` | `NA` |
| ICS-20 transfer | `Scheduled` (ibc-go team) | `??` | `NA` | `Scheduled` | `NA` |
| Changes in IBC-GO testing suite | `Scheduled` (ibc-go team) | `NA` | `Partial coverage` | `NA` | `NA` |

## Integration with Cosmos SDK

A prerequisite of the code review is to open a PR with all the [SDK changes](https://github.com/cosmos/cosmos-sdk/tree/interchain-security-rebase) needed by Interchain Security.

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Changes to staking module | `Scheduled` (sdk team) | `Partial coverage` <br /> see [unbonding_test.go](../x/ccv/provider/unbonding_test.go) <br />  redelegation and validator unbonding missing | `Partial coverage` | `Scheduled` | `NA` |
| Changes to slashing module | `Scheduled` (sdk team) | `??` | `NA` | `Scheduled` | `NA` |
| Changes to evidence module | `Scheduled` (sdk team) | `??` | `NA` | `Scheduled` | `NA` |

## Provider Chain Correctness

The main concern addressed in this section is the correctness of the provider chain (e.g., the Cosmos Hub). In other words, when Interchain Security is enabled (i.e., the provider CCV module is enabled), the safety and liveness properties still hold. This _**MUST**_ be the case regardless of the number of consumer chains, i.e., 
- no consumer chain;
- one single consumer chain;
- multiple consumer chains.

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Liveness of undelegations <br /> - unbonding delegation entries are eventually removed from `UnbondingDelegation` | `Scheduled` | `Done` <br /> see [unbonding_test.go](../x/ccv/provider/unbonding_test.go) | `Done` | `Scheduled` | `Scheduled` |
| Liveness of redelegations <br /> - redelegations entries are eventually removed from `Redelegations` | `Scheduled` | `Scheduled` | `Scheduled` | `Scheduled` | `??` |
| Liveness of validator unbondings <br /> - unbonding validators with no delegations are eventually removed from `Validators` | `Scheduled` | `Scheduled` | `Done` | `Scheduled` | `??` |
| Unbonding operations (undelegations, redelegations, validator unbondings) should eventually complete even if the CCV channel is never established (due to error) | `Scheduled` | `??` | `Future work` | `Scheduled` | `??` |
| A validator cannot get slashed more than once for double signing, regardless of how many times it double signs on different chains (consumers or provider) | `Scheduled` | `??` | `Done` | `Scheduled` | `NA` |
| A validator cannot get slashed multiple times for downtime on the same chain without requesting to `Unjail` itself in between | `Scheduled` | `??` | `Partial coverage` | `Scheduled` | `NA` |
| A validator can be slashed multiple times for downtime on different chains | `Scheduled` | `??` | `NA` | `Scheduled` | `NA` |
| The provider chain can easily be restarted with IS enabled <br /> - `ExportGenesis` & `InitGenesis` | `Scheduled` | `??` | `Future work` | `Scheduled` | `NA` |
| The provider chain can graciously handle a CCV packet timing out (without shuting down) <br /> (expected outcome) consumer chain shuts down and its state in provider CCV module is removed | `Scheduled` | `??` | `Future work` | `Scheduled` | `NA` |
| The provider chain can graciously handle a `StopConsumerChainProposal` <br /> (expected outcome) consumer chain shuts down and its state in provider CCV module is removed | `Scheduled` | `??` | `Future work` | `Scheduled` | `NA` |
| The provider chain can graciously handle a `SpawnConsumerChainProposal` <br /> (expected outcome) a consumer chain is added and a client is created | `Scheduled` | `??` | `Future work` | `Scheduled` | `NA` |

## Interchain Security Protocol Correctness

The main concern addressed in this section is the correctness of the Interchain Security protocol. In other words, the implementation should be aligned with the Interchain Security [specification](https://github.com/cosmos/ibc/blob/master/spec/appics-028-cross-chain-validation/README.md). 

The implementation MUST guarantee the *Channel Uniqueness* property, i.e., the channel between the provider chain and a consumer chain MUST be unique.

In addition, the implementation MUST guarantee the following [system properties](https://github.com/cosmos/ibc/blob/master/spec/appics-028-cross-chain-validation/system_model_and_properties.md#system-properties):
- *Validator Set Replication*
- *Bond-Based Consumer Voting Power*
- *Slashable Consumer Misbehavior*
- *Consumer Rewards Distribution*

---

| Concern re. *Channel Uniqueness* | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| `SpawnConsumerChainProposal(chainId)` should fail if a consumer with `chainId` already exists | `Scheduled` | `??` | `NA` | `Scheduled` | `Scheduled` |
| The channel handshake for a consumer with `chainId` should fail if there is already an established CCV channel for `chainId`  | `Scheduled` | `??` | `NA` | `Scheduled` | `NA` |
| *Channel Uniqueness* should hold even if a consumer chain restarts | `Scheduled` | `??` | `NA` | `Scheduled` | `NA` |
| *Channel Uniqueness* should hold even when a client expires | `Scheduled` | `??` | `NA` | `Scheduled` | `NA` |

---

| Concern re. *Validator Set Replication* | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Every validator set on any consumer chain MUST either be or have been a validator set on the provider chain. | `Scheduled` | `NA` | `Done` | `Scheduled` | `??` |
| Any update in the power of a validator `val` on the provider, as a result of <br /> - (increase) `Delegate()` / `Redelegate()` to `val` <br /> - (increase) `val` joining the provider validator set <br /> - (decrease) `Undelegate()` / `Redelegate()` from `val` <br /> - (decrease) `Slash(val)` <br /> - (decrease) `val` leaving the provider validator set <br /> MUST be present in a `ValidatorSetChangePacket` that is sent to all consumer chains | `Scheduled` | `NA` | `Done` | `Scheduled` | `??` |
| Every consumer chain receives the same sequence of `ValidatorSetChangePacket`s in the same order. | `Scheduled` | `NA` | `NA` | `Scheduled` | `Scheduled` |

---

| Concern re. *Bond-Based Consumer Voting Power* | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| For every `ValidatorSetChangePacket` received by a consumer chain at time `t`, a `MaturedVSCPacket` is sent back to the provider in the first block with a timestamp `>= t + UnbondingPeriod` | `Scheduled` | `Scheduled` | `Done` | `Scheduled` | `??` |
| If an unbonding operation resulted in a `ValidatorSetChangePacket` sent to all registered consumer chains, then it cannot complete before receiving matching `MaturedVSCPacket`s from these consumer chains (unless some of these consumer chains are removed) | `Scheduled` | `Scheduled` | `Done` | `Scheduled` | `??` |
| TBA ...

---

| Concern re. *Slashable Consumer Misbehavior* | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Multiple downtime infractions committed by the same validator `val` on the same consumer chain without `val` requesting to `Unjail` itself result in a single `SlashPacket` | `Scheduled` | `??` | `Done` | `Scheduled` | `??` |
| If evidence of misbehavior is submitted on a consumer chain within the unbonding period targeting an amount `x` of staked tokens, the amount `x` cannot be unlocked on the provider before the corresponding `SlashPacket` is received <br /> - `SlashPacket` will not arrive after the corresponding `MaturedVSCPacket`s | `Scheduled` | `??` | `Done` | `Scheduled` | `??` |
| TBA ...

---

| Concern re. *Consumer Rewards Distribution* | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Validators on the provider chain receive rewards for participating in IS | `Scheduled` | `Scheduled` | `NA` | `Scheduled` | `NA` |
| The rewards sent to the provider chain are escrowed on the consumer chains (no double spend) | `Scheduled` | `Scheduled` | `NA` | `Scheduled` | `NA` |

---

## Consumer Chain Correctness

The main concern addressed in this section is the correctness of the consumer chains. In other words, when Interchain Security is enabled (i.e., the consumer CCV module is enabled), the safety and liveness properties still hold. This also covers various flavor of consumer chains:
- minimum viable consumer chain ([mvcc](https://github.com/cosmos/interchain-security/issues/139))
- governance-enabled consumer chain ([gov-cc](https://github.com/cosmos/interchain-security/issues/141)), with the modified staking and distribution modules (see `x/ccv/staking` and `x/ccv/distribution`); also, must look at the [atom-gov module](https://github.com/cosmos/interchain-security/issues/162)
- CosmWasm-enabled consumer chain ([wasm-cc](https://github.com/cosmos/interchain-security/issues/143)), with the CosmWasm module enabled

> TODO create clear concerns for `gov-cc` and `wasm-cc` once the implementations are done

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Consumer chain liveness (blocks are being produced) | `Scheduled` | `NA` | `??` | `Scheduled` | `NA` |
| A chain has the ability to restart as a consumer chain with no more than 24 hours downtime | `Scheduled` | `NA` | `??` | `Scheduled` | `NA` |
| Governance on `gov-cc` | `Scheduled` | `??` | `??` | `Scheduled` | `NA` |
| CosmWasm on `wasm-cc` | `Scheduled` | `??` | `??` | `Scheduled` | `NA` |
| TBA ...

> TODO Scenarios to consider for restarting chains, client expiration
>   - A consumer chain restarts as a normal chain (after shutting down, either controlled or due to timing out)
>   - A consumer chain restarts as a consumer chain (after shutting down, either controlled or due to timing out)
