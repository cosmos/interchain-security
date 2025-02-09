---
sidebar_position: 2
---


# Reward Distribution

Sending and distributing rewards from consumer chains to the provider chain is handled by the [Reward Distribution sub-protocol](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#reward-distribution).

Consumer chains have the option of sharing _a portion of_ their block rewards (inflation tokens and fees) with the provider chain as ICS rewards.
These rewards are periodically sent from the consumer to the provider according to [consumer chain parameters](../build/modules/03-consumer.md#parameters) using an IBC transfer channel.
This channel is created during consumer chain initialization, unless it is provided when creating a new consumer chain (see the [DistributionTransmissionChannel param](../build/modules/03-consumer.md#distributiontransmissionchannel)). 

Providing an IBC transfer channel enables a consumer chain to reuse one of the existing channels to the provider for consumer chain rewards distribution. 
This will preserve the `ibc denom` that may already be in use. 
This is especially important for standalone chains transitioning to become consumer chains. 
For more details, see the [changeover procedure](../consumer-development/changeover-procedure.md).

Once on the provider, the ICS rewards are distributed to the opted in validators and their delegators.
Note that rewards are **only** distributed to validators that are opted in and have been validating the consumer chain
for a continuous number of epochs (see `NumberOfEpochsToStartReceivingRewards` param).

To avoid spam, the provider must whitelist denoms before accepting them as ICS rewards.  

## Reward distribution with power capping

If a consumer chain has set a [validators-power cap](./power-shaping.md#capping-the-validator-powers), then the total received
rewards are distributed proportionally to validators with respect to their capped voting power on the consumer and **not**
with respect to their voting power on the provider.

For example, assume that the provider chain has 4 validators, `A`, `B`, `C`, and `D` with voting powers 100, 1, 1, 1 respectively.
So, validators `A`, `B`, `C`, and `D` have ~97%, ~1%, ~1%, and ~1% of the total voting power of the provider respectively.
Now, assume that all those 4 validators opt in on a consumer chain that has set a validators-power cap set to 30%.
As a result, validators `A`, `B`, `C`, and `D` have their powers modified (only) on the consumer chain to 
30, 25, 24, and 24 and now have ~29%, ~25%, ~23%, and ~23% of the total voting power of the consumer.
Roughly speaking, when rewards are sent from the consumer to the provider, validator `A` would get ~29% of the rewards
because it has 29% of the total voting power on the consumer, regardless of `A`'s 97% of the total power on the provider.
Similarly, validator `B` would get 25% of the rewards, etc.


## Whitelisting Reward Denoms

The ICS distribution system works by allowing consumer chains to send rewards to a module address on the provider called the `ConsumerRewardsPool`.
Only whitelisted denoms from the `ConsumerRewardsPool` are then distributed to validators and their delegators.

The whitelisted denoms can be adjusted through governance by sending a `MsgChangeRewardDenoms` message.
`MsgChangeRewardDenoms` is used to update the set of denoms accepted by the provider as rewards.
Note that a `MsgChangeRewardDenoms` is only accepted on the provider chain if at least one of the `denomsToAdd` or `denomsToRemove` fields is populated with at least one denom.
Also, a denom cannot be repeated in both sets.

An example of a `MsgChangeRewardDenoms` message:
```js
{
 "@type": "/interchain_security.ccv.provider.v1.MsgChangeRewardDenoms",
 "denoms_to_add": [
  "ibc/42C7464F6415DC7529A8C7581FE0991C7A090D60176BC90998B1DAF75B868635"
 ],
 "denoms_to_remove": [],
 "authority": "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn"
}
```

Besides native provider denoms (e.g., `uatom` for the Cosmos Hub), please use the `ibc/*` denom trace format.
For example, for `untrn` transferred over the path `transfer/channel-569`, the denom trace can be queried using the following command:
```bash
> gaiad query ibc-transfer denom-hash transfer/channel-569/untrn
hash: 0025F8A87464A471E66B234C4F93AEC5B4DA3D42D7986451A059273426290DD5
```
Then use the resulting hash when adding or removing denoms. For example:

```js
 "denoms_to_add": [
  "ibc/0025F8A87464A471E66B234C4F93AEC5B4DA3D42D7986451A059273426290DD5"
 ]
```

To query the list of whitelisted reward denoms on the Cosmos Hub, use the following command:
```bash
> gaiad q provider registered-consumer-reward-denoms
denoms:
- ibc/0025F8A87464A471E66B234C4F93AEC5B4DA3D42D7986451A059273426290DD5
- ibc/6B8A3F5C2AD51CD6171FA41A7E8C35AD594AB69226438DB94450436EA57B3A89
- uatom
```

:::tip
Use the following command to get a human readable denom from the `ibc/*` denom trace format:
```bash
>  gaiad query ibc-transfer denom-trace ibc/0025F8A87464A471E66B234C4F93AEC5B4DA3D42D7986451A059273426290DD5
denom_trace:
  base_denom: untrn
  path: transfer/channel-569
```
:::
