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
| Unexpected panics | `TODO` | `??` | `??` |
| Handling errors | `TODO` | `gosec` | `??` |
| Accessing store (setters, getters, iterators) | `TODO` | `??` | `Low coverage` |
| Serialization / deserialization | `TODO` | `??` | `??` |
| Storage leaks | `TODO` | `NA` | `??` |

## Integration with IBC

Interchain Security is an IBC application and, thus, it relies on IBC to establish a separate channel between the provider chain and every consumer chain. Interchain Security relies on the IBC v3.0 golang [implementation](https://github.com/cosmos/ibc-go/tree/v3.0.0).

IBC packets:
- ValidatorSetChangePacket
- MaturedVSCPacket
- SlashPacketData

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Create IBC clients | `TODO` (ibc-go team) | `Done` | `Future work` | `TODO` | `NA` |
| Getting consumer `UnbondingPeriod` from IBC client | `TODO` (ibc-go team) | `??` | `Not planned` | `TODO` | `NA` |
| Create CCV channel (handshake) | `TODO` (ibc-go team) | `Done` | `Future work` | `TODO` | `TODO` |
| Sending IBC packets <br /> - see `x/ccv/utils/utils.go:SendIBCPacket()` | `TODO` (ibc-go team) | `Done` | `Done` | `TODO` | `NA` |
| Handling acknowledgments | `TODO` (ibc-go team) | `Low coverage` | `Scheduled` | `TODO` | `NA` |
| Handling timeouts | `TODO` (ibc-go team) | `Low coverage` | `Future work` | `TODO` | `NA` |
| Handling IBC client expiration | `TODO` (ibc-go team) | `??` | `Future work` | `TODO` | `NA` |
| ICS-20 channel creation | `TODO` (ibc-go team) | `??` | `Future work` | `TODO` | `NA` |
| ICS-20 transfer | `TODO` (ibc-go team) | `??` | `Not planned` | `TODO` | `NA` |

## Integration with Cosmos SDK

A prerequisite of the code review is to open a PR with all the [SDK changes](https://github.com/cosmos/cosmos-sdk/tree/interchain-security-rebase) needed by Interchain Security.

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Changes to staking module | `TODO` (sdk team) | `Low coverage` | `Partially done` | `TODO` | `NA` |
| Changes to slashing module | `TODO` (sdk team) | `??` | `??` | `TODO` | `NA` |
| Changes to evidence module | `TODO` (sdk team) | `??` | `??` | `TODO` | `NA` |

## Provider Chain Correctness

The main concern addressed in this section is the correctness of the provider chain (e.g., the Cosmos Hub). In other words, when Interchain Security is enabled (i.e., the provider CCV module is enabled), the safety and liveness properties still hold. This _**MUST**_ be the case regardless of the number of consumer chains, i.e., 
- no consumer chain;
- one single consumer chain;
- multiple consumer chains.

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Liveness of undelegations <br /> - unbonding delegation entries are eventually removed from `UnbondingDelegation` | `TODO` | `Done` | `Done` | `TODO` | `TODO` |
| Liveness of redelegations <br /> - redelegations entries are eventually removed from `Redelegations` | `TODO` | `TODO` | `Scheduled` | `TODO` | `TODO` |
| Liveness of validator unbondings <br /> - unbonding validators with no delegations are eventually removed from `Validators` | `TODO` | `TODO` | `Done` | `TODO` | `TODO` |
| Unbonding operations (undelegations, redelegations, validator unbondings) should eventually complete even if the CCV channel is never established (due to error) | `TODO` | `TODO` | `Future work` | `TODO` | `TODO` |
| A validator cannot get slashed more than once for double signing, regardless of how many times it double signs on different chains (consumers or provider) | `TODO` | `??` | `Done` | `TODO` | `TODO` |
| A validator cannot get slashed multiple times for downtime on the same chain without requesting to `Unjail` itself in between | `TODO` | `??` | `Partially done` | `TODO` | `TODO` |
| A validator can be slashed multiple times for downtime on different chains | `TODO` | `??` | `Not planned` | `TODO` | `TODO` |
| The provider chain can easily be restarted with IS enabled <br /> - `ExportGenesis` & `InitGenesis` | `TODO` | `??` | `Future work` | `TODO` | `NA` |
| The provider chain can graciously handle a CCV packet timing out (without shuting down) <br /> (expected outcome) consumer chain shuts down and its state in provider CCV module is removed | `TODO` | `??` | `Future work | `TODO` | `NA` |
| The provider chain can graciously handle a `StopConsumerChainProposal` <br /> (expected outcome) consumer chain shuts down and its state in provider CCV module is removed | `TODO` | `??` | `Future work` | `TODO` | `NA` |
| The provider chain can graciously handle a `SpawnConsumerChainProposal` <br /> (expected outcome) a consumer chain is added and a client is created | `TODO` | `??` | `Future work` | `TODO` | `NA` |

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
| `SpawnConsumerChainProposal(chainId)` should fail if a consumer with `chainId` already exists | `TODO` | `??` | `Not planned` | `TODO` | `TODO` |
| The channel handshake for a consumer with `chainId` should fail if there is already an established CCV channel for `chainId`  | `TODO` | `??` | `Not planned` | `TODO` | `TODO` |
| *Channel Uniqueness* should hold even if a consumer chain restarts | `TODO` | `??` | `Not planned` | `TODO` | `TODO` |
| *Channel Uniqueness* should hold even when a client expires | `TODO` | `??` | `Not planned` | `TODO` | `TODO` |

---

| Concern re. *Validator Set Replication* | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Every validator set on any consumer chain MUST either be or have been a validator set on the provider chain. | `TODO` | `NA` | `Done` | `TODO` | `TODO` |
| Every consumer chain receives the same sequence of `ValidatorSetChangePacket`s in the same order. | `TODO` | `NA` | `Not planned` | `TODO` | `TODO` |

---

| Concern re. *Bond-Based Consumer Voting Power* | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| All power increases of a validator `val` on a consumer chain are because of <br /> - a `Delegate()` / `Redelegate()` to `val` on provider <br /> - `val` joining the provider validator set (another validator leaving the set) | `TODO` | `TODO` | `??` | `TODO` | `TODO` |
| All power decreases of a validator `val` on a consumer chain are because of <br /> - an `Undelegate()` / `Redelegate()` from `val` on provider <br /> - `val` gets slashed on the provider chain <br /> - another validator joining the provider validator set (`val` leaving the set) | `TODO` | `TODO` | `??` | `TODO` | `TODO` |
| In the case of a power change of a validator `val` on a consumer chain at time `t` the corresponding tokens remain locked on the provider chain until at least `t + UnbondingPeriod` or are slashed | `TODO` | `TODO` | `Done` | `TODO` | `TODO` |
| TBA ...

---

| Concern re. *Slashable Consumer Misbehavior* | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Multiple downtime infractions committed by the same validator `val` on the same consumer chain without `val` requesting to `Unjail` itself result in a single `SlashPacket` | `TODO` | `TODO` | `Done` | `TODO` | `TODO` |
| If evidence of misbehavior is submitted on a consumer chain within the unbonding period targeting an amount `x` of staked tokens, the amount `x` cannot be unlocked on the provider before the corresponding `SlashPacket` is received <br /> - `SlashPacket` will not arrive after the corresponding `MaturedVSCPacket`s | `TODO` | `TODO` | `Done` | `TODO` | `TODO` |
| TBA ...

---

| Concern re. *Consumer Rewards Distribution* | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Validators on the provider chain receive rewards for participating in IS | `TODO` | `TODO` | `Not planned` | `TODO` | `NA` |
| The rewards sent to the provider chain are escrowed on the consumer chains (no double spend) | `TODO` | `TODO` | `Not planned` | `TODO` | `NA` |

---

## Consumer Chain Correctness

The main concern addressed in this section is the correctness of the consumer chains. In other words, when Interchain Security is enabled (i.e., the consumer CCV module is enabled), the safety and liveness properties still hold. This also covers various flavor of consumer chains:
- minimum viable consumer chain ([mvcc](https://github.com/cosmos/interchain-security/issues/139))
- governance-enabled consumer chain ([gov-cc](https://github.com/cosmos/interchain-security/issues/141)), with the modified staking and distribution modules (see `x/ccv/staking` and `x/ccv/distribution`); also, must look at the [atom-gov module](https://github.com/cosmos/interchain-security/issues/162)
- CosmWasm-enabled consumer chain ([wasm-cc](https://github.com/cosmos/interchain-security/issues/143)), with the CosmWasm module enabled

> TODO create clear concerns for `gov-cc` and `wasm-cc` once the implementations are done

| Concern | Code Review | Unit Testing | Diff. testing | Testnet | Protocol audit |
| ------- | ----------- | ------------ | ------------- | ------- | ----- |
| Consumer chain liveness (blocks are being produced) | `TODO` | `NA` | `??` | `TODO` | `NA` |
| A chain has the ability to restart as a consumer chain with no more than 24 hours downtime | `TODO` | `NA` | `??` | `TODO` | `NA` |
| Governance on `gov-cc` | `TODO` | `??` | `??` | `TODO` | `NA` |
| CosmWasm on `wasm-cc` | `TODO` | `??` | `??` | `TODO` | `NA` |
| TBA ...

> TODO Scenarios to consider for restarting chains, client expiration
>   - A consumer chain restarts as a normal chain (after shutting down, either controlled or due to timing out)
>   - A consumer chain restarts as a consumer chain (after shutting down, either controlled or due to timing out)