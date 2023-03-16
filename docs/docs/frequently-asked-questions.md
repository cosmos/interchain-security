---
sidebar_position: 4
title: "Frequently Asked Questions"
slug: /faq
---

## What is the meaning of Validator Set Replication?
VSR simply means that the same validator set is used to secure both the provider and consumer chains. VSR is ensured through ICS protocol which keeps consumers up to date with the validator set of the provider.

## What even is a consumer chain?

Consumer chain is blockchain operated by the same the same validator operators as the provider chain. The ICS protocol ensures the validator set replication properties (informs consumer chain about the current state of the validator set on the provider)

Consumer chains are run on infrastructure (virtual or phyisical machines) distinct from the provider, have their own configurations and operating requirements.

## What happens to consumer if provider is down?
In case the provider chain halts or experiences difficulties the consumer chain will keep operating - the provider chain and consumer chains represent different networks, which only share the validator set.

The consumer chain will not halt if the provider halts because they represent distinct networks and distinct infrastructures. Provider chain liveness does not impact consumer chain liveness.

However, if the `trusting_period` (currently 5 days for protocol safety reasons) elapses without receiving any updates from the provider, the consumer chain will essentially transition to a Proof of Authority chain.
This means that the validator set on the consumer will be the last validator set of the provider that the consumer knows about.

Steps to recover from this scenario and steps to "release" the validators from their duties will be specified at a later point.
At the very least, the consumer chain could replace the validator set, remove the ICS module and perform a genesis restart. The impact of this on the IBC clients and connections is currently under careful consideration.

## What happens to provider if consumer is down?
Consumer chains do not impact the provider chain.
The ICS protocol is concerned only with validator set replication and the only communication that the provider requires from the consumer is information about validator activity (essentially keeping the provider informed about slash events).

## Can I run the provider and consumer chains on the same machine?
Yes, but you should favor running them in separate environments so failure of one machine does not impact your whole operation.

## Can the consumer chain have its own token?
As any other cosmos-sdk chain the consumer chain can issue its own token, manage inflation parameters and use them to pay gas fees.

## How are Tx fees paid on consumer?
The consumer chain operates as any other cosmos-sdk chain. The ICS protocol does not impact the normal chain operations.

## Are there any restrictions the consumer chains need to abide by?
No. Consumer chains are free to choose how they wish to operate, which modules to include, use CosmWASM in a permissioned or a permissionless way.
The only thing that separates consumer chains from sovereign chains is that they share their validator set with the provider chain.

## What's in it for the stakers?
The consumer chains sends a portion of its fees and inflation as reward to the provider chain as defined by `consumer_redistribution_fraction`. The rewards are distributed (sent to the provider) every `blocks_per_distribution_transmission`.

:::tip
  `consumer_redistribution_fraction` and `blocks_per_distribution_transmission` are parameters defined in the `ConsumerAdditionProposal` used to create the consumer chain. These parameters can be changed via consumer chain governance.
:::

## What's in it for the validators?
The consumer chains sends a portion of its fees and inflation as reward to the provider chain as defined by `consumer_redistribution_fraction`. The rewards are distributed (sent to the provider) every `blocks_per_distribution_transmission`.

:::tip
  `consumer_redistribution_fraction` and `blocks_per_distribution_transmission` are parameters defined in the `ConsumerAdditionProposal` used to create the consumer chain. These parameters can be changed via consumer chain governance.
:::


## Can the consumer chain have its own governance?
**Yes.**

In that case the validators are not necessarily part of the governance structure. Instead, their place in governance is replaced by "representatives" (governors). The representatives do not need to run validators, they simply represent the interests of a particular interest group.

Validators can also be representatives but representatives are not required to run validator nodes.

This feature discerns between validator operators (infrastructure) and governance representatives which further democratizes the ecosystem. This also reduces the pressure on validators to be involved in on-chain governance.


## Validator Opt-out?
:::tip
There are multiple opt-out mechanisms being considered such as soft opt-in -> allows bottom 20% of the validator to not run all consumer chains thereby reducing their operating costs.
:::
## How Equivocation Governance Slashing works?
:::tip
To avoid potential attacks directed at provider chain validators, a new mechanism was introduced:

When a validator double-signs on the provider chain a special type of slash packet is relayed to the provider chain. The provider will store information about the double signing validator and allow a governance proposal to be submitted.
If the double-signing proposal passes, the offending validator will be slashed on the provider chain and tombstoned. Tombstoning will permanently exclude the validator from the active set of the provider.

An equivocation proposal cannot be submitted for a validator that did not double sign on any of the consumer chains.
:::
## Can Consumer Chains Perform Software Upgrades?
Consumer chains are essentially sovereign chains, in the sense that they can run arbitrary logic and use any modules they want (ie CosmWASM).

Consumer chain upgrades are unlikely to impact the provider chain, as long as there are no changes to the ICS module.

## How can I connect to the testnets?
Multiple testnets are active
- list discord
- GoC notes

## How to start using ICS?
To become a consumer chain use this checklist

## Supported relayers?
Currently supported versions:
- Hermes 1.3

## How key delegation works in ICS?
New feature that allows validators to use different private keys depending on network.

Txs to submit
Queries to check the key

Adds an additional security layer.

The provider chain tracks all keys and knows how to map between them for double signing/downtime slashing
