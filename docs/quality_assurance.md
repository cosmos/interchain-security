# Interchain Security: Quality Assurance

This document contains the overview of the quality assurance process necessary for the release of Interchain Security v1.

The quality assurance of Interchain Security is done using the following approaches:

- code review
- automatic software engineering tools (e.g., SonarCloud, gosec)
- unit testing
- integration tests
- differential testing using heuristics
- incentivized testnet
- protocol audit (with the Apalache team from Informal Systems)

The quality assurance of Interchain Security is split across the following concerns:

- Correct software engineering (e.g., error handling, serialization, deserialization).
- The correct integration with IBC (i.e., [ibc-go](https://github.com/cosmos/ibc-go/tree/v3.0.0)).
- The correct integration with Cosmos SDK (i.e., [cosmos-sdk](https://github.com/cosmos/cosmos-sdk/tree/v0.45.6)).
- The correctness of the provider chain, i.e., the provider CCV module does not break the liveness or the safety of the provider chain.
- The correctness of the Interchain Security protocol, i.e., the protocol follows the [specification](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/README.md).
- The correctness of the consumer chain, i.e., both liveness or safety hold.

For an overview of the Interchain Security workflow, have a look at [the diagrams](#interchain-security-workflow) at the end of this document.

## Quality Assurance Concerns

### Software Engineering

| ID | Concern | Code Review | Automatic Tools | Unit Testing |
| -- | ------- | ----------- | --------------- | ------------ |
| 1.01 | Unexpected panics | `Scheduled` | `NA` | `NA` |
| 1.02 | Handling errors | `Scheduled` | `gosec` | `Partial coverage` |
| 1.03 | Accessing store (setters, getters, iterators) | `Scheduled` | `NA` | `Partial coverage` |
| 1.04 | Serialization / deserialization | `Scheduled` | `NA` | `Partial coverage` |
| 1.05 | Storage leaks | `Scheduled` | `NA` | `NA` |

### Integration with IBC

Interchain Security is an IBC application and, thus, it relies on IBC to establish a separate channel between the provider chain and every consumer chain. Interchain Security relies on the IBC v3.0 golang [implementation](https://github.com/cosmos/ibc-go/tree/v3.0.0).

IBC packets:

- ValidatorSetChangePacket
- MaturedVSCPacket
- SlashPacketData

| ID | Concern | Code Review | Unit Testing | E2E Testing | Diff. Testing | Testnet |
| -- | ------- | ----------- | ------------ | ----------- | ------------- | ------- |
| 2.01 | Create IBC clients | `Scheduled` (ibc-go) | `Done` [TestCreateConsumerClient](../x/ccv/provider/keeper/proposal_test.go#117), [TestInitGenesis](../x/ccv/consumer/keeper/genesis_test.go#26) | `Done` [SetupTest](../tests/e2e/setup_test.go#39), [TestConsumerGenesis](../tests/e2e/channel_init_test.go#21) | `Future work` | `Scheduled` |
| 2.02 | Create CCV channel (handshake) | `Scheduled` (ibc-go) | `Done` [provider/ibc_module_test.go](../x/ccv/provider/ibc_module_test.go), [consumer/ibc_module_test.go](../x/ccv/consumer/ibc_module_test.go) | `Done` [SetupCCVChannel](../tests/e2e/setup_test.go#125) | `Future work` | `Scheduled` |
| 2.03 | Sending IBC packets <br> [SendIBCPacket](../x/ccv/utils/utils.go#40) | `Scheduled` (ibc-go) | `NA` | `Done` [TestSendVSCMaturedPackets](../tests/e2e/valset_update_test.go#39), [TestSendSlashPacket](../tests/e2e/slashing_test.go#648) | `Done` | `Scheduled` |
| 2.04 | Handling acknowledgments | `Scheduled` (ibc-go) | [Scheduled](https://github.com/cosmos/interchain-security/issues/362) | `Partial coverage` [TestOnAcknowledgementPacket](../x/ccv/consumer/keeper/relay_test.go#152), [TestSlashPacketAcknowldgement](../tests/e2e/slashing_test.go#258) | `Done` | `Scheduled` |
| 2.05 | Handling timeouts | `Scheduled` (ibc-go) | [Scheduled](https://github.com/cosmos/interchain-security/issues/362) |`NA` | `Future work` | `Scheduled` |
| 2.06 | Handling IBC client expiration <br> - high priority| `Scheduled` (ibc-go)  | `NA` | `NA` | `Future work` | `Scheduled` |
| 2.07 | ICS-20 channel creation | `Scheduled` (ibc-go) | `NA` | `Done` [SetupTransferChannel](../tests/e2e/setup_test.go#152) |`Future work` | `Scheduled` |
| 2.08 | ICS-20 transfer | `Scheduled` (ibc-go) | `NA` | `Done` [TestRewardsDistribution](../tests/e2e/distribution_test.go#17) | `NA` | `Scheduled` |
| 2.09 | Changes in IBC-GO testing suite | `Scheduled` (ibc-go) | `NA` | `NA` | `Partial coverage` | `NA` |

### Integration with Cosmos SDK

- [x] A prerequisite of the code review is to open a PR with all the [SDK changes](https://github.com/cosmos/cosmos-sdk/tree/interchain-security-rebase) needed by Interchain Security.

| ID | Concern | Code Review | Unit Testing | E2E Testing | Diff. Testing | Testnet |
| -- | ------- | ----------- | ------------ | ----------- | ------------- | ------- |
| 3.01 | Changes to staking module | `Done` | `Done` (Cosmos-SDK side) | `Partial coverage` <br> [unbonding_test.go](../tests/e2e/unbonding_test.go) <br> redelegation could be expanded, validator unbonding missing | `Partial coverage` | `Scheduled` |
| 3.02 | Changes to slashing module | `Done` | `NA` | `Done` <br> [TestValidatorDowntime](../tests/e2e/slashing_test.go#L502) <br>  | `Partial coverage` | `Scheduled` |
| 3.03 | Changes to evidence module | `Done` | `NA` | `Done` <br> [TestValidatorDoubleSigning](../tests/e2e/slashing_test.go#L584) <br>  | `NA` | `Scheduled` |

### Provider Chain Correctness

The main concern addressed in this section is the correctness of the provider chain (e.g., the Cosmos Hub). In other words, when Interchain Security is enabled (i.e., the provider CCV module is enabled), the safety and liveness properties still hold. This _**MUST**_ be the case regardless of the number of consumer chains, i.e.,

- no consumer chain;
- one single consumer chain;
- multiple consumer chains.

| ID | Concern | Code Review | Unit Testing | E2e | Diff. Testing | Testnet | Protocol audit |
| -- | ------- | ----------- | ------------ | --- | ------------- | ------- | -------------- |
| 4.01 | Liveness of undelegations <br> - unbonding delegation entries are eventually removed from `UnbondingDelegation` | `Scheduled` | `NA` | `Done` <br> [unbonding_test.go](../tests/e2e/unbonding_test.go) | `Done` | `Scheduled` | `NA` |
| 4.02 | Liveness of redelegations <br> - redelegations entries are eventually removed from `Redelegations` | `Scheduled` | `NA` | `Scheduled` | `Scheduled` | `Scheduled` | `NA` |
| 4.03 | Liveness of validator unbondings <br> - unbonding validators with no delegations are eventually removed from `Validators` | `Scheduled` | `NA` | `NA` | `Done` | `Scheduled` | `NA` |
| 4.04 | Unbonding operations (undelegations, redelegations, validator unbondings) should eventually complete even if the CCV channel is never established (due to error) <br> - expected outcome: the channel initialization sub-protocol eventually times out, which leads to the consumer chain removal | `Scheduled` | `NA` | `Done` [TestUndelegationDuringInit](../tests/e2e/unbonding_test.go#145) | `Future work` | `Scheduled` | `Done` |
| 4.05 | Unbonding operations (undelegations, redelegations, validator unbondings) should eventually complete even if one of the clients expire <br> - expected outcome: the pending VSC packets eventually timeout, which leads to the consumer chain removal | `Scheduled` | `NA` | `Done` [TestUndelegationVscTimeout](../tests/e2e/unbonding.go#127) | `Future work` | `Scheduled` | `NA` |
| 4.06 | A validator cannot get slashed more than once for double signing, regardless of how many times it double signs on different chains (consumers or provider) | `Scheduled` | `NA` |`Done` <br> [TestHandleSlashPacketErrors](../tests/e2e/slashing_test.go#L317) | `Done` | `Scheduled` | `NA` |
| 4.07 | A validator cannot get slashed multiple times for downtime on the same consumer chain without requesting to `Unjail` itself on the provider chain in between | `Scheduled` | `NA` | `Partial coverage` <br> [TestSendSlashPacket](../tests/e2e/slashing_test.go#L648) | `Partial coverage` | `Scheduled` | `NA` |
| 4.08 | A validator can be slashed multiple times for downtime on different chains | `Scheduled` | `NA` | `Future work` | `NA` | `Scheduled` | `NA` |
| 4.09 | The provider chain can easily be restarted with IS enabled <br> - `ExportGenesis` & `InitGenesis`  <br> - requires https://github.com/informalsystems/hermes/issues/1152| `Scheduled` | `Done` <br> [TestInitAndExportGenesis](../x/ccv/provider/keeper/genesis_test.go#L20) | `Future work` | `Future work` | `Scheduled` | `NA` |
| 4.10 | The provider chain can graciously handle a CCV packet timing out (without shuting down) <br> - expected outcome: consumer chain shuts down and its state in provider CCV module is removed | `Scheduled` | `Scheduled` | `NA` | `Future work` | `Scheduled` | `NA` |
| 4.11 | The provider chain can graciously handle a `ConsumerRemovalProposal` <br> - expected outcome: consumer chain shuts down and its state in provider CCV module is removed | `Scheduled` | `Done` <br> [TestHandleConsumerRemovalProposal](../x/ccv/provider/keeper/proposal_test.go#L313) | `NA` | `Future work` | `Scheduled` | `NA` |
| 4.12 | The provider chain can graciously handle a `ConsumerAdditionProposal` <br> - expected outcome: a consumer chain is registered and a client is created | `Scheduled` |`Done` <br> [TestHandleConsumerAdditionProposal](../x/ccv/provider/keeper/proposal_test.go#L31) | `NA` | `Future work` | `Scheduled` | `NA` |

### Interchain Security Protocol Correctness

The main concern addressed in this section is the correctness of the Interchain Security protocol. In other words, the implementation should be aligned with the Interchain Security [specification](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/README.md).

The implementation MUST guarantee the _Channel Uniqueness_ property, i.e., the channel between the provider chain and a consumer chain MUST be unique.

In addition, the implementation MUST guarantee the following [system properties](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties):

- _Validator Set Replication_
- _Bond-Based Consumer Voting Power_
- _Slashable Consumer Misbehavior_
- _Consumer Rewards Distribution_

---

| ID | Concern re. _Channel Uniqueness_ | Code Review | Unit Testing | E2e Testing | Diff. Testing | Testnet | Protocol audit |
| -- | -------------------------------- | ----------- | ------------ | ----------- | ------------- | ------- | -------------- |
| 5.01 | `HandleConsumerAdditionProposal()` should fail if a consumer with `chainId` is already registered | `Scheduled` | `Done` [TestCreateConsumerClient](../x/ccv/provider/keeper/proposal_test.go#L116) | `NA` | `NA` | `Scheduled` | `NA` |
| 5.02 | The channel handshake for a consumer with `chainId` should fail if there is already an established CCV channel for `chainId`  | `Scheduled` | `Done` [TestOnChanOpenTry](../x/ccv/provider/ibc_module_test.go#L103), [TestOnChanOpenInit](../x/ccv/consumer/ibc_module_test.go#L59) | `NA` | `NA` | `Scheduled` | `NA` |
| 5.03 | _Channel Uniqueness_ should hold even if a consumer chain restarts | `Scheduled` | `NA` | `Scheduled` | `NA` | `Scheduled` | `NA` |
| 5.04 | _Channel Uniqueness_ should hold even when a client expires | `Scheduled` | `NA` | `Scheduled` | `NA` | `Scheduled` | `NA` |

---

| ID | Concern re. _Validator Set Replication_ | Code Review | Unit Testing | E2e Testing | Diff. testing | Testnet | Protocol audit |
| -- | --------------------------------------- | ----------- | ------------ | ----------- | ------------- | ------- | -------------- |
| 6.01 | Every validator set on any consumer chain MUST either be or have been a validator set on the provider chain. | `Scheduled` | `NA` | `NA` | `Done` | `Scheduled` | `Scheduled` |
| 6.02 | Any update in the power of a validator `val` on the provider, as a result of <br> - (increase) `Delegate()` / `Redelegate()` to `val` <br> - (increase) `val` joining the provider validator set <br> - (decrease) `Undelegate()` / `Redelegate()` from `val` <br> - (decrease) `Slash(val)` <br> - (decrease) `val` leaving the provider validator set <br> MUST be present in a `ValidatorSetChangePacket` that is sent to all registered consumer chains | `Scheduled` | `NA` | `NA` | `Done` | `Scheduled` | `Scheduled` |
| 6.03 | Every consumer chain receives the same sequence of `ValidatorSetChangePacket`s in the same order. | `Scheduled` | `NA` | `NA` | `NA` | `Scheduled` | `Scheduled` <br> high priority |

---

| ID | Concern re. _Bond-Based Consumer Voting Power_ | Code Review | Unit Testing | E2e Testing | Diff. Testing | Testnet | Protocol audit |
| -- | ---------------------------------------------- | ----------- | ------------ | ----------- | ------------- | ------- | -------------- |
| 7.01 | For every `ValidatorSetChangePacket` received by a consumer chain at time `t`, a `MaturedVSCPacket` is sent back to the provider in the first block with a timestamp `>= t + UnbondingPeriod` | `Scheduled` | `NA` | `NA` | `Done` | `Scheduled` | `Scheduled` |
| 7.02 | If an unbonding operation resulted in a `ValidatorSetChangePacket` sent to all registered consumer chains, then it cannot complete before receiving matching `MaturedVSCPacket`s from these consumer chains (unless some of these consumer chains are removed) | `Scheduled` | `NA` | `NA` | `Done` | `Scheduled` | `Scheduled` |

---

| ID | Concern re. _Slashable Consumer Misbehavior_ | Code Review | Unit Testing | E2e Testing | Diff. testing | Testnet | Protocol audit |
| -- | -------------------------------------------- | ----------- | ------------ | ----------- | ------------- | ------- | -------------- |
| 8.01 | Multiple downtime infractions committed by the same validator `val` on the same consumer chain without `val` requesting to `Unjail` itself result in a single `SlashPacket` | `Scheduled` | `NA` | `NA` | `Done` | `Scheduled` | `NA` |
| 8.02 | If evidence of misbehavior is submitted on a consumer chain within the unbonding period targeting an amount `x` of staked tokens, the amount `x` cannot be unlocked on the provider before the corresponding `SlashPacket` is received <br> - `SlashPacket` will not arrive after the corresponding `MaturedVSCPacket`s | `Scheduled` | `NA` | `NA` | `Done` | `Scheduled` | `NA` |

---

| ID | Concern re. _Consumer Rewards Distribution_ | Code Review | Unit Testing | E2e Testing | Diff. testing | Testnet | Protocol audit |
| -- | ------------------------------------------- | ----------- | ------------ | ----------- | ------------- | ------- | -------------- |
| 9.01 | Validators on the provider chain receive rewards for participating in IS | `Scheduled` | `NA` | `Done` [TestRewardsDistribution](../tests/e2e/distribution_test.go#17) | `NA` | `Scheduled` | `NA` |
| 9.02 | The rewards sent to the provider chain are escrowed on the consumer chains (no double spend) | `Scheduled` | `NA` | `Scheduled` | `NA` | `Scheduled` | `NA` |

---

### Consumer Chain Correctness

The main concern addressed in this section is the correctness of the consumer chains. In other words, when Interchain Security is enabled (i.e., the consumer CCV module is enabled), the safety and liveness properties still hold. This also covers various flavor of consumer chains:

- minimum viable consumer chain ([mvcc](https://github.com/cosmos/interchain-security/issues/139))
- governance-enabled consumer chain ([gov-cc](https://github.com/cosmos/interchain-security/issues/141)), with the modified staking and distribution modules (see `x/ccv/staking` and `x/ccv/distribution`); also, must look at the [atom-gov module](https://github.com/cosmos/interchain-security/issues/162)
- CosmWasm-enabled consumer chain ([wasm-cc](https://github.com/cosmos/interchain-security/issues/143)), with the CosmWasm module enabled

| ID | Concern | Code Review | Unit Testing | E2e Testing | Diff. testing | Testnet | Protocol audit |
| -- | ------- | ----------- | ------------ | ----------- | ------------- | ------- | -------------- |
| 10.01 | Consumer chain liveness (blocks are being produced) | `Scheduled` | `NA` | `NA` | `NA` | `Scheduled` | `NA` |
| 10.02 | A chain has the ability to restart as a consumer chain with no more than 24 hours downtime | `Scheduled` | `NA` | `NA` | `NA` | `Scheduled` | `NA` |
| 10.03 | A consumer chain has the ability to restart as a normal chain after shutting down, either controlled (via `ConsumerRemovalProposal`) or due to timing out | `Scheduled` | `NA` | `NA` | `NA` | `Scheduled` | `NA` |
| 10.04 | A consumer chain has the ability to restart as a consumer chain with the same `chainId` after shutting down, either controlled (via `ConsumerRemovalProposal`) or due to timing out | `Scheduled` | `NA` | `Scheduled` | `NA` | `Scheduled` | `NA` |
| 10.05 | Governance on `gov-cc` | `Scheduled` | `NA` | `Partial Coverage` [TestDemocracyGovernanceWhitelisting](../tests/e2e/distribution_test.go#133) | `Scheduled` | `Scheduled` | `NA` |
| 10.06 | CosmWasm on `wasm-cc` | `Scheduled` | `NA` | `Scheduled` | `NA` | `Scheduled` | `NA` |
| TBA ...

> TODO create clear concerns for `gov-cc` and `wasm-cc` once the implementations are done

## Interchain Security Workflow

The following diagrams show (in orange) the events that influence the operation of Interchain Security -- during creating consumer chains, normal operation, and removing consumer chains. These events are the result of actions that can be performed by the existing actors, i.e., users (token holders), validators, and relayers.

![Creating Consumer Chains](./figures/is_init_overview.png?raw=true)

![Normal Operation](./figures/is_normalop_overview.png?raw=true)

![Remove Consumer Chains](./figures/is_remove_overview.png?raw=true)
