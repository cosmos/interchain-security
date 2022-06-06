# Business requirements

> TODO

# User requirements

## Use cases

### Custom Consumer Chain

> TODO

### Contract Consumer Chains

> TODO

### Governance-Gated CosmWasm Consumer Chains

> TODO

# Functional requirements

> TODO

## Assumptions

1. Interchain Security packets will never timeout.

## Features

### 1 - Bootstrapping

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 1.01 | A chain has the ability to enable or disable Interchain Security functionality in the genesis state. | Covered by 1.01.x | See 1.01.x | v1 |
| 1.01.01 | A chain has the ability to enable or disable Interchain Security **_provider_** functionality in the genesis state. | TBA |  `Not Implemented` | v1 |
| 1.01.02 | A chain has the ability to enable or disable Interchain Security **_consumer_** functionality in the genesis state. | TBA |  `Implemented` | v1 |
| 1.02 | A provider chain has the ability to bootstrap a new consumer chain as a result of passing a governance proposal to spawn that consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/proposal_handler_test.go#L16) | `Implemented` | v1 |
| 1.02.01 | A provider chain has the ability to create a client to every accepted consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/proposal_handler_test.go#L16) | `Implemented` | v1 |
| 1.03 | A provider chain has the ability to create the genesis state for every accepted consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/keeper/proposal_test.go#L17) | `Implemented` | v1 |
| 1.04 | A consumer chain has the ability to start from a genesis state without an existing CCV channel to a provider chain (i.e., the chain has not previously established a CCV channel to a provider chain). | TBA | `Implemented` | v1 |
| 1.04.01 | A consumer chain has the ability to create a client to the provider chain. | TBA | `Implemented` | v1 |
| 1.05 | Enable the channel opening handshake between the provider chain and every accepted consumer chain. | Covered by 1.04.x | `Implemented` | v1 |
| 1.05.01 | Enable `OnChanOpenInit` logic on every accepted consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/consumer/module_test.go#L104) | `Implemented` | v1 |
| 1.05.02 | Enable `OnChanOpenTry` logic on the provider chain for every accepted consumer chain. | `None` | `Implemented` | v1 |
| 1.05.03 | Enable `OnChanOpenAck` logic on every accepted consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/consumer/module_test.go#L246) | `Implemented` | v1 |
| 1.05.04 | Enable `OnChanOpenConfirm` logic on the provider chain for every accepted consumer chain. | `None` | `Implemented` | v1 |


### 2 - Core 

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 2.01 | **Validator Set Update**: A provider chain has the ability to provide validator set updates to all registered consumer chains with established CCV channels. | TBA | `Implemented` | v1 |
| 2.02 | **Timely Completion of Unbonding Operations**: A provider chain has the ability to timely complete all unbonding operations, i.e., the completion must wait for the `UnbondingPeriod` to elapse on all the registered consumer chains. | Covered by 2.02.x  | `Implemented` | v1 |
| 2.02.01 | The completion of undelegations must wait for the `UnbondingPeriod` to elapse on all the registered consumer chains. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/unbonding_hook_test.go) | `Implemented` | v1 |
| 2.02.02 | The completion of redelegations must wait for the `UnbondingPeriod` to elapse on all the registered consumer chains. | `None` | `Implemented` | v1 |
| 2.02.03 | The completion of validator unbondings must wait for the `UnbondingPeriod` to elapse on all the registered consumer chains. | `None` | `Implemented` | v1 |
| 2.02.04 | The completion of unbonding operations on the provider chain is not affected by Interchain Security when there is no registered consumer chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/unbonding_hook_test.go#L251) | `Implemented` | v1 |
| 2.03 | **Consumer Initiated Slashing**: The validators participating in Interchain Security are punished accordingly for infractions on the consumer chains. | Covered by 2.03.x | `Implemented` | v1 | `Implemented` | v1 |
| 2.03.01 | The validators participating in Interchain Security are punished accordingly for **_downtime_** infractions on the consumer chains. | TBA | `Implemented` | v1 | `Implemented` | v1 |
| 2.03.02 | The validators participating in Interchain Security are punished accordingly for **_double-signing_** infractions on the consumer chains. | TBA | `Implemented` | v1 |
| 2.04 | **Simple Reward Distribution**: The validators participating in Interchain Security receive rewards (i.e., block production rewards and transaction fees) for validating on the consumer chains. | TBA | `Implemented` | v1 |

### 3 - Restart and Upgrade

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 3.01 | Enable the provider chain to export its Interchain Security state. | `None` | `Implemented` (see [#121](https://github.com/cosmos/interchain-security/issues/121)) | v1 |
| 3.02 | Enable the provider chain to restart from a previously exported genesis state. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/provider/keeper/genesis_test.go#L10)  | `Implemented` | v1 |
| 3.03 | Enable the consumer chain to export its Interchain Security state. | `None` | `Implemented` (see [#121](https://github.com/cosmos/interchain-security/issues/121)) | v1 |
| 3.04 | Enable the consumer chain to restart from a previously exported genesis state with an existing channel to a provider chain. | [Unit Testing](https://github.com/cosmos/interchain-security/blob/579db08d6bb34ea2f5ad793841f66f464935f6bb/x/ccv/consumer/keeper/genesis_test.go#L19) | `Implemented` | v1 |


### 4 - Removal and Cleanup

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 4.01 | Enable the provider chain to handle governance proposals to stop certain consumer chains. | TBA | `WIP` | v1 |
| TBA | Enable the channel closing handshake between the provider chain and every accepted consumer chain. | TBA | `Implemented` | v1 |


### 5 - Provider Chain

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 5.01 | Enable **_once_** opting out from Interchain Security: The provider chain validators have the ability to decide (before joining the validator set on the provider chain) whether they want to participate in Interchain Security, i.e., validate also on the consumer chains. | `None` | `Not Implemented` | v1 |

### 6 - Custom Consumer Chain

| ID  | Description | Verification | Status | Release |
| --- | ----------- | ------------ | ------ | ------- |
| 6.01 | A chain has the ability to become a consumer chain with no more than `24h` downtime. | TBA | `Implemented` | v1 |

# Non-functional requirements

> TODO

# External interface requirements

> TODO