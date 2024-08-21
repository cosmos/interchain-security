---
sidebar_position: 2
---


# Reward Distribution

Sending and distributing rewards from consumer chains to the provider chain is handled by the [Reward Distribution sub-protocol](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#reward-distribution).

Consumer chains have the option of sharing _a portion of_ their block rewards (inflation tokens and fees) with the provider chain as ICS rewards.
These rewards are periodically sent from the consumer to the provider according to [consumer chain parameters](../introduction/params.md#reward-distribution-parameters) using an IBC transfer channel.
This channel is created during consumer chain initialization, unless it is provided when creating a new consumer chain (see the [DistributionTransmissionChannel param](../introduction/params.md#distributiontransmissionchannel)). 

Providing an IBC transfer channel enables a consumer chain to re-use one of the existing channels to the provider for consumer chain rewards distribution. 
This will preserve the `ibc denom` that may already be in use. 
This is especially important for standalone chains transitioning to become consumer chains. 
For more details, see the [changeover procedure](../consumer-development/changeover-procedure.md).

Once on the provider, the ICS rewards are distributed to the opted in validators and their delegators. 
To avoid spam, the provider must whitelist denoms before accepting them as ICS rewards.  

## Whitelisting Reward Denoms

The ICS distribution system works by allowing consumer chains to send rewards to a module address on the provider called the `ConsumerRewardsPool`.
Only whitelisted denoms are transferred from the `ConsumerRewardsPool` to the `FeePoolAddress`, to be distributed to validators and their delegators.
The whitelisted denoms can be adjusted through governance by sending a [`ChangeRewardDenomProposal`](./proposals.md#changerewarddenomproposal).

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