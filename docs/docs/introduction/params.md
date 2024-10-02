---
sidebar_position: 3
---

# Interchain Security Parameters

The parameters necessary for Interchain Security (ICS) are defined in 

- the `Params` structure in `proto/interchain_security/ccv/provider/v1/provider.proto` for the provider;
- the `ConsumerParams` structure in `proto/interchain_security/ccv/v1/shared_consumer.proto` for the consumer.

## Time-Based Parameters

ICS relies on the following time-based parameters.

### ProviderUnbondingPeriod
`ProviderUnbondingPeriod` is the unbonding period on the provider chain as configured during chain genesis.
This parameter can later be changed via governance.

###  ConsumerUnbondingPeriod
`ConsumerUnbondingPeriod` is the unbonding period on the consumer chain.

:::info
`ConsumerUnbondingPeriod` is set via the `unbonding_period` field in `ConsumerInitializationParameters` when creating or
updating the consumer.
It is recommended that every consumer chain set and unbonding period shorter than `ProviderUnbondingPeriod`
<br></br>

Example:
```
ConsumerUnbondingPeriod = ProviderUnbondingPeriod - one week
```
:::


### CCVTimeoutPeriod
`CCVTimeoutPeriod` is the period used to compute the timeout timestamp when sending IBC packets. 

For more details, see the [IBC specification of Channel & Packet Semantics](https://github.com/cosmos/ibc/blob/main/spec/core/ics-004-channel-and-packet-semantics/README.md#sending-packets).

:::warning
If a sent packet is not relayed within this period, then the packet times out. The CCV channel used by the interchain security protocol is closed, and the corresponding consumer is removed.
:::

CCVTimeoutPeriod may have different values on the provider and consumer chains.
- `CCVTimeoutPeriod` on the provider **must** be larger than `ConsumerUnbondingPeriod`
- `CCVTimeoutPeriod` on the consumer is initial set via the `ConsumerInitializationParameters`

### BlocksPerDistributionTransmission
`BlocksPerDistributionTransmission` is the number of blocks on the consumer chain that have to pass for the consumer to
send an IBC transfer containing the rewards to the provider.

### TransferPeriodTimeout
`TransferPeriodTimeout` is the period used to compute the timeout timestamp when sending IBC transfer packets from a consumer to the provider.

If this timeout expires, then the transfer is attempted again after `BlocksPerDistributionTransmission` blocks.
- `TransferPeriodTimeout` on the consumer is initial set via the `ConsumerInitializationParameters` when creating or updating the consumer
- `TransferPeriodTimeout` should be smaller than `BlocksPerDistributionTransmission x avg_block_time`


## Reward Distribution Parameters

:::tip
The following chain parameters dictate consumer chain distribution amount and frequency.
They are set at consumer genesis and `BlocksPerDistributionTransmission`, `ConsumerRedistributionFraction`
`TransferTimeoutPeriod` must be provided in every `ConsumerChainAddition` proposal.
:::


### ConsumerRedistributionFraction

`ConsumerRedistributionFraction` is the fraction of tokens allocated to the consumer redistribution address during distribution events. The fraction is a string representing a decimal number. For example `"0.75"` would represent `75%`.

:::tip
Example:

With `ConsumerRedistributionFraction` set to `"0.75"` the consumer chain would send `75%` of its block rewards and accumulated fees to the consumer redistribution address, and the remaining `25%` to the provider chain every `BlocksPerDistributionTransmission` blocks.
:::

### DistributionTransmissionChannel

`DistributionTransmissionChannel` is the provider chain IBC channel used for receiving consumer chain reward distribution token transfers. This is automatically set during the consumer-provider handshake procedure.

### ProviderFeePoolAddrStr

`ProviderFeePoolAddrStr` is the provider chain fee pool address used for receiving consumer chain reward distribution token transfers. This is automatically set during the consumer-provider handshake procedure.


## Slash Throttle Parameters
For preventing malicious consumer chains from harming the provider, [slash throttling](../adrs/adr-002-throttle.md) (also known as _jail throttling_)
ensures that only a fraction of the provider validator set can be jailed at any given time. Slash throttling is configurable using the following parameters.

### SlashMeterReplenishPeriod
`SlashMeterReplenishPeriod` exists on the provider such that once the slash meter becomes not-full, the slash meter is replenished after this period has elapsed.

The meter is replenished to an amount equal to the slash meter allowance for that block, or `SlashMeterReplenishFraction * CurrentTotalVotingPower`.

### SlashMeterReplenishFraction
`SlashMeterReplenishFraction` exists on the provider as the portion (in range [0, 1]) of total voting power that is replenished to the slash meter when a replenishment occurs.

This param also serves as a maximum fraction of total voting power that the slash meter can hold. The param is set/persisted as a string, and converted to a `sdk.Dec` when used.

### RetryDelayPeriod

`RetryDelayPeriod` exists on the consumer for **ICS versions >= v3.2.0** (introduced by the implementation of [ADR-008](../adrs/adr-008-throttle-retries.md)) and is the period at which the consumer retries to send a `SlashPacket` that was rejected by the provider.


## Epoch Parameters

### BlocksPerEpoch
`BlocksPerEpoch` exists on the provider for **ICS versions >= 3.3.0** (introduced by the implementation of [ADR-014](../adrs/adr-014-epochs.md))
and corresponds to the number of blocks that constitute an epoch. This param is set to 600 by default. Assuming we need 6 seconds to
commit a block, the duration of an epoch corresponds to 1 hour. This means that a `VSCPacket` would be sent to a consumer
chain once at the end of every epoch, so once every 600 blocks. This parameter can be adjusted via a governance proposal,
however careful consideration is needed so that `BlocksPerEpoch` is not too large, because we also need to consider
potential slow chain upgrades that could delay the sending of a `VSCPacket`, as well as potential increases in the time
it takes to commit a block (e.g., from 6 seconds to 30 seconds).