---
sidebar_position: 3
---

# Interchain Security Parameters

The parameters necessary for Interchain Security (ICS) are defined in 

- the `Params` structure in `proto/interchain_security/ccv/provider/v1/provider.proto` for the provider;
- the `Params` structure in `proto/interchain_security/ccv/consumer/v1/consumer.proto` for the consumer.

## Time-based parameters

ICS relies on the following time-based parameters.

### ProviderUnbondingPeriod
is the unbonding period on the provider chain as configured during chain genesis. This parameter can later be changed via governance.

###  ConsumerUnbondingPeriod
is the unbonding period on the consumer chain.

:::info
`ConsumerUnbondingPeriod` is set via the `ConsumerAdditionProposal` governance proposal to add a new consumer chain.
It is recommended that every consumer chain set and unbonding period shorter than `ProviderUnbondingPeriod`
<br></br>

Example:
```
ConsumerUnbondingPeriod = ProviderUnbondingPeriod - one day
```
:::

Unbonding operations (such as undelegations) are completed on the provider only after the unbonding period elapses on every consumer.


### TrustingPeriodFraction
is used to calculate the `TrustingPeriod` of created IBC clients on both provider and consumer chains.  


Setting `TrustingPeriodFraction` to `0.5` would result in the following:
```
TrustingPeriodFraction = 0.5
ProviderClientOnConsumerTrustingPeriod = ProviderUnbondingPeriod * 0.5
ConsumerClientOnProviderTrustingPeriod = ConsumerUnbondingPeriod * 0.5
```

Note that a light clients must be updated within the `TrustingPeriod` in order to avoid being frozen.

For more details, see the [IBC specification of Tendermint clients](https://github.com/cosmos/ibc/blob/main/spec/client/ics-007-tendermint-client/README.md).

### CCVTimeoutPeriod
is the period used to compute the timeout timestamp when sending IBC packets. 

For more details, see the [IBC specification of Channel & Packet Semantics](https://github.com/cosmos/ibc/blob/main/spec/core/ics-004-channel-and-packet-semantics/README.md#sending-packets).

:::warning
If a sent packet is not relayed within this period, then the packet times out. The CCV channel used by the interchain security protocol is closed, and the corresponding consumer is removed.
:::

CCVTimeoutPeriod may have different values on the provider and consumer chains.
- `CCVTimeoutPeriod` on the provider **must** be larger than `ConsumerUnbondingPeriod`
- `CCVTimeoutPeriod` on the consumer is initial set via the `ConsumerAdditionProposal`

### InitTimeoutPeriod
is the maximum allowed duration for CCV channel initialization to execute.

For any consumer chain, if the CCV channel is not established within `InitTimeoutPeriod` then the consumer chain will be removed and therefore will not be secured by the provider chain.

The countdown starts when the `spawn_time` specified in the `ConsumerAdditionProposal` is reached.

### `VscTimeoutPeriod`
is the provider-side param that enables the provider to timeout VSC packets even when a consumer chain is not live.
If the `VscTimeoutPeriod` is ever reached for a consumer chain that chain will be considered not live and removed from interchain security.

:::tip
`VscTimeoutPeriod` MUST be larger than the `ConsumerUnbondingPeriod`.
:::

### BlocksPerDistributionTransmission
is the number of blocks between rewards transfers from the consumer to the provider.

### TransferPeriodTimeout
is the period used to compute the timeout timestamp when sending IBC transfer packets from a consumer to the provider.

If this timeout expires, then the transfer is attempted again after `BlocksPerDistributionTransmission` blocks.
- `TransferPeriodTimeout` on the consumer is initial set via the `ConsumerAdditionProposal` gov proposal to add the consumer
- `TransferPeriodTimeout` should be smaller than `BlocksPerDistributionTransmission x avg_block_time`


## Slash Throttle Parameters

### SlashMeterReplenishPeriod
exists on the provider such that once the slash meter becomes not-full, the slash meter is replenished after this period has elapsed.

The meter is replenished to an amount equal to the slash meter allowance for that block, or `SlashMeterReplenishFraction * CurrentTotalVotingPower`.

### SlashMeterReplenishFraction
exists on the provider as the portion (in range [0, 1]) of total voting power that is replenished to the slash meter when a replenishment occurs.

This param also serves as a maximum fraction of total voting power that the slash meter can hold. The param is set/persisted as a string, and converted to a `sdkmath.LegacyDec` when used.

### MaxThrottledPackets
exists on the provider as the maximum amount of throttled slash or vsc matured packets that can be queued from a single consumer before the provider chain halts, it should be set to a large value.

This param would allow provider binaries to panic deterministically in the event that packet throttling results in a large amount of state-bloat. In such a scenario, packet throttling could prevent a violation of safety caused by a malicious consumer, at the cost of provider liveness.
