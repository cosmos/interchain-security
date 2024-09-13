---
sidebar_position: 3
---

# x/consumer

## Overview

The ICS consumer module enables consumer chains to use stake locked on a provider chain 
as collateral for their own proof-of-stake based block production. 

The consumer module established a IBC ordered channel to the provider chain. 
This channel is used by the provider chain to regularly sent validator updates the the consumer chain. 
The consumer sends these updates to its own consensus engine. 
This means that the consumer module acts as a staking module of the consumer chain. 

Regularly, the consumer module sends a part of the consumer chain's block rewards 
to the provider chain as ICS rewards.

If one of the validators in the consumer chain's validator set is missing enough blocks (i.e., downtime infraction),
the consumer module notifies the provider chain by sending an IBC packet to the provider module. 
As a result, the misbehaving validator is punished on the provider chain.

## State 

## State Transitions

## Messages

### MsgUpdateParams

`MsgUpdateParams` updates the [consumer module parameters](#parameters). 
The params are updated through a governance proposal where the signer is the gov module account address.

```proto
message MsgUpdateParams {
  option (cosmos.msg.v1.signer) = "authority";

  // signer is the address of the governance account.
  string authority = 1 [(cosmos_proto.scalar) = "cosmos.AddressString"];

  // params defines the x/consumer parameters to update.
  interchain_security.ccv.v1.ConsumerParams params = 2 [(gogoproto.nullable) = false];
}
```

## Begin-Block

## End-Block

## Hooks

## Events

## Parameters

:::warning
The consumer module parameters are set by the provider when creating the consumer genesis (i.e., when launching the consumer chain). 
As a result, changes of these parameters might results in incompatibilities between different versions of consumers and providers. 
:::

The consumer module contains the following parameters.

### Enabled

`Enabled` is deprecated. 

### BlocksPerDistributionTransmission


| Type  | Default value |
| ----- | ------------- |
| int64 | 1000          |

`BlocksPerDistributionTransmission` is the number of blocks between rewards transfers from the consumer to the provider.

### DistributionTransmissionChannel

| Type   | Default value |
| ------ | ------------- |
| string | ""            |

`DistributionTransmissionChannel` is the provider chain IBC channel used for receiving consumer chain reward distribution token transfers. This is automatically set during the consumer-provider handshake procedure.

Providing an IBC transfer channel enables a consumer chain to re-use one of the existing channels to the provider for consumer chain rewards distribution. 
This will preserve the `ibc denom` that may already be in use. 
This is especially important for standalone chains transitioning to become consumer chains. 
For more details, see the [changeover procedure](../consumer-development/changeover-procedure.md).

### ProviderFeePoolAddrStr

| Type   | Default value |
| ------ | ------------- |
| string | ""            |

`ProviderFeePoolAddrStr` is the provider chain fee pool address used for receiving consumer chain reward distribution token transfers. This is automatically set during the consumer-provider handshake procedure.

### CcvTimeoutPeriod

| Type          | Default value      |
| ------------- | ------------------ |
| time.Duration | 2419200s (4 weeks) |

`CcvTimeoutPeriod` is the period used to compute the timeout timestamp when sending IBC packets. 
`CcvTimeoutPeriod` may have different values on the provider and consumer chains.

### TransferTimeoutPeriod

| Type          | Default value  |
| ------------- | -------------- |
| time.Duration | 3600s (1 hour) |

`TransferTimeoutPeriod` is the timeout period for consumer chain reward distribution IBC packets.

### ConsumerRedistributionFraction

| Type   | Default value |
| ------ | ------------- |
| string | "0.75"        |

`ConsumerRedistributionFraction` is the fraction of tokens allocated to the consumer redistribution address during distribution events. 
The fraction is a string representing a decimal number. For example `"0.75"` would represent `75%`.
For example, a consumer with `ConsumerRedistributionFraction` set to `"0.75"` would send `75%` of its block rewards and accumulated fees to the consumer redistribution address, and the remaining `25%` to the provider chain every `BlocksPerDistributionTransmission` blocks.

### HistoricalEntries

| Type  | Default value |
| ----- | ------------- |
| int64 | 10000         |

`HistoricalEntries` is the number of historical info entries to persist in store (see the staking module parameter with the same name for details). 
`HistoricalEntries` is needed since the consumer module acts as a staking module on the consumer chain.

### UnbondingPeriod

| Type          | Default value      |
| ------------- | ------------------ |
| time.Duration | 1209600s (2 weeks) |

`UnbondingPeriod` is the unbonding period on the consumer chain.
It is recommended that every consumer chain set and unbonding period shorter than provider unbonding period, e.g., one week shorter. 

### SoftOptOutThreshold

`SoftOptOutThreshold` is deprecated.

### RewardDenoms

| Type     | Default value |
| -------- | ------------- |
| []string | []string{}    |

`RewardDenoms` are the denominations which are allowed to be sent to the provider as ICS rewards.

### ProviderRewardDenoms

| Type     | Default value |
| -------- | ------------- |
| []string | []string{}    |

`ProviderRewardDenoms` are the denominations coming from the provider which are allowed to be used as ICS rewards. e.g. "uatom".

### RetryDelayPeriod

| Type          | Default value  |
| ------------- | -------------- |
| time.Duration | 3600s (1 hour) |

`RetryDelayPeriod` is the period at which the consumer retries to send a `SlashPacket` that was rejected by the provider.
For more details, see [ADR-008](../adrs/adr-008-throttle-retries.md).

## Client