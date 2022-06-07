# Business requirements

> TODO

# User requirements

## Use cases

### Custom Consumer Chain

> TODO e.g., Quicksilver

### Contract Consumer Chains

> TODO e.g., TBA 

### Governance-Gated CosmWasm Consumer Chains

> TODO e.g., Lido

# Functional requirements

## Assumptions

1. Interchain Security packets will (almost) never timeout.

## Features

### 1 - Bootstrapping

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 1.01 | A chain has the ability to enable or disable Interchain Security functionality in the genesis state. | Covered by 1.01.x | See 1.01.x | v1 |
| 1.01.01 | A chain has the ability to enable or disable Interchain Security **_provider_** functionality in the genesis state. | `None` |  `Not Implemented` | TBA |
| 1.01.02 | A chain has the ability to enable or disable Interchain Security **_consumer_** functionality in the genesis state. | TBA |  `Implemented` | v1 |
| 1.02 | A provider chain has the ability to register a new consumer chain as a result of passing a governance proposal to spawn that consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/proposal_handler_test.go#L16) | `Implemented` | v1 |
| 1.02.01 | A provider chain has the ability to create a client to every registered consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/proposal_handler_test.go#L16) | `Implemented` | v1 |
| 1.03 | A provider chain has the ability to create the genesis state for every registered consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/keeper/proposal_test.go#L17) | `Implemented` | v1 |
| 1.04 | A consumer chain has the ability to start from a genesis state without an existing CCV channel to a provider chain (i.e., the chain has not previously established a CCV channel to a provider chain). | TBA | `Implemented` | v1 |
| 1.04.01 | A consumer chain has the ability to create a client to the provider chain. | TBA | `Implemented` | v1 |
| 1.05 | Enable the channel opening handshake between the provider chain and every registered consumer chain. | Covered by 1.04.x | `Implemented` | v1 |
| 1.05.01 | Enable `OnChanOpenInit` logic on every registered consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/consumer/module_test.go#L104) | `Implemented` | v1 |
| 1.05.02 | Enable `OnChanOpenTry` logic on the provider chain for every registered consumer chain. | `None` | `Implemented` | v1 |
| 1.05.03 | Enable `OnChanOpenAck` logic on every registered consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/consumer/module_test.go#L246) | `Implemented` | v1 |
| 1.05.04 | Enable `OnChanOpenConfirm` logic on the provider chain for every registered consumer chain. | `None` | `Implemented` | v1 |

### 2 - Core 

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 2.01 | **Validator Set Update**: A provider chain has the ability to provide validator set updates to all registered consumer chains with established CCV channels. | TBA | `Implemented` | v1 |
| 2.01.01 | A provider chain has the ability to store validator set updates for every registered consumer chain during the process of establishing the CCV channel and then, provide these validator set updates once the CCV channel is established. | TBA | `WIP` | v1 |
| 2.02 | **Timely Completion of Unbonding Operations**: A provider chain has the ability to timely complete all unbonding operations, i.e., the completion must wait for the `UnbondingPeriod` to elapse on all the registered consumer chains. | Covered by 2.02.x  | `Implemented` | v1 |
| 2.02.01 | The completion of undelegations must wait for the `UnbondingPeriod` to elapse on all the registered consumer chains. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/unbonding_hook_test.go) | `Implemented` | v1 |
| 2.02.02 | The completion of redelegations must wait for the `UnbondingPeriod` to elapse on all the registered consumer chains. | `None` | `Implemented` | v1 |
| 2.02.03 | The completion of validator unbondings must wait for the `UnbondingPeriod` to elapse on all the registered consumer chains. | `None` | `Implemented` | v1 |
| 2.02.04 | The completion of unbonding operations on the provider chain is not affected by Interchain Security when there is no registered consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/unbonding_hook_test.go#L251) | `Implemented` | v1 |
| 2.02.05 | The completion of unbonding operations on the provider chain is blocked during the process of establishing a CCV channel to an registered consumer chain. | TBA | `WIP` | v1 |
| 2.03 | **Consumer Initiated Slashing**: A provider chain has the ability to punish the validators participating in Interchain Security for infractions committed on the consumer chains. | Covered by 2.03.x | See 2.03.x | v1 |
| 2.03.01 | A provider chain has the ability to punish the validators participating in Interchain Security for **_downtime_** infractions committed on the consumer chains. | TBA | `Implemented` | v1 |
| 2.03.02 | A provider chain has the ability to punish the validators participating in Interchain Security for **double-signing** infractions committed on the consumer chains. | TBA | `Implemented` | v1 |
| 2.04 | **Simple Reward Distribution**: A provider chain has the ability to receive rewards (i.e., block production rewards and transaction fees) from registered consumer chains and distribute these rewards to the validators participating in Interchain Security. | TBA | `Implemented` | v1 |

### 3 - Restart and Upgrade

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 3.01 | A provider chain has the ability to export its Interchain Security state. | `None` | `Implemented` (see [#121](https://github.com/cosmos/interchain-security/issues/121)) | v1 |
| 3.02 | A provider chain has the ability to restart from a previously exported genesis state. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/keeper/genesis_test.go#L10)  | `Implemented` | v1 |
| 3.03 | A consumer chain has the ability to export its Interchain Security state. | `None` | `Implemented` (see [#121](https://github.com/cosmos/interchain-security/issues/121)) | v1 |
| 3.04 | A consumer chain has the ability to restart from a previously exported genesis state with an existing channel to a provider chain. (Notice this feature is different from 1.04.) | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/consumer/keeper/genesis_test.go#L19) | `Implemented` | v1 |


### 4 - Removal and Cleanup

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 4.01 | A provider chain has the ability to remove a registered consumer chain as a result of passing a governance proposal to stop that consumer chain. This also entails that the provider chain has the ability to properly clean up the Interchain Security state. | TBA | `WIP` | v1 |
| 4.02 | A provider chain has the ability to remove a registered consumer chain as a result of an IBC packet sent to that consumer chain timing out. (Notice that, since the CCV channel is ordered, a packet timing out results in the CCV channel being closed). | TBA | `WIP` | v1 |
| 4.02.01 | The proposer of a consumer chain has the ability to enable or disable the locking of unbonding operations in the case a timeout occurs. | TBA | `WIP` | v1 |
| 4.03 | A consumer chain must shut down once the established CCV channel is closed. | TBA | `WIP` | v1 |
| 4.04 | When shutting down, a consumer chain has the ability to export a valid genesis state that can be used afterwards to restart the chain. | `None` | `Not Implemented` | TBA |

### 5 - Provider Chain

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 5.01 | Enable **_once_** opting out from Interchain Security: The provider chain validators have the ability to decide (before joining the validator set on the provider chain) whether they want to participate in Interchain Security, i.e., validate also on the consumer chains. | `None` | `Not Implemented` | TBA |

### 6 - Consumer Chain

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 6.01 | A chain has the ability to restart as a consumer chain with no more than `24` hours downtime. | TBA | `Implemented` | v1 |
| 6.02 | **Consumer governance enabled by provider token**: A consumer chain has the ability to process certain governance proposals that passed the voting on the provider chain. Notice that this enables the consumer chain to use the token staked on the provider chain as the governance token. | `None` | `Not Implemented` | TBA |
| 6.03 | **Consumer governance enabled by native token**: A consumer chain has the ability to have its own native token that can be used as a governance token. | `None` | `WIP` | v1 |
| 6.03.01 | A consumer chain has the ability to inflate its own native token. | `None` | `Implemented` | v1 |
| 6.03.02 | The holders of the native token of a consumer chain have the ability to stake the token in order to participate in the governance of the consumer chain. | `None` | `Implemented` | v1 |
| 6.03.03 | A consumer chain has the ability to distribute (inflationary) rewards to the stakers of the native token. | `None` | `WIP` | v1 |
| 6.04 | **CosmWasm-enabled consumer chain**: A consumer chain has the ability to run CosmWasm smart contracts. | `None` | `WIP` | v1 |
| 6.05 | **EVM-enabled consumer chain**: A consumer chain has the ability to run EVM smart contracts. | `None` | `Not Implemented` | TBA |

# Non-functional requirements

## Assumptions

See the Assumptions section [ICS 28](https://github.com/cosmos/ibc/blob/marius/ccv/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#assumptions) standard document.  

## Features

### 7 - Security

For more details of the following features, see the System Properties section of the [ICS 28](https://github.com/cosmos/ibc/blob/marius/ccv/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties) standard document.  

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 7.01 | Validator Set Replication | `None` | `Implemented` | v1 |
| 7.02 | Bond-Based Consumer Voting Power | `None` | `Implemented` | v1 |
| 7.03 | Slashable Consumer Misbehavior | `None` | `Implemented` | v1 |
| 7.04 | Consumer Rewards Distribution | `None` | `Implemented` | v1 |
| 7.05 | A consumer chain must disable all transactions, except the ones containing IBC messages, until the CCV channel is established. | `None` | `WIP` | v1 |

# External interface requirements

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| | There shall be a CLI command to query a proposer chain for the genesis state of every registered consumer chain. | TBA | `Implemented` | v1 |
| | Users have the ability to use a CLI tool that enables them to deploy a Contract Consumer Chain. | `None` | `WIP` | v1 |