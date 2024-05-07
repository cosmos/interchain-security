---
sidebar_position: 5
title: "Frequently Asked Questions"
slug: /faq
---

## What is a consumer chain?

Consumer chain is blockchain operated by (a subset of) the validators of the provider chain. The ICS protocol ensures that the consumer chain gets information about which validators should run it (informs consumer chain about the current state of the validator set and the opted in validators for this consumer chain on the provider).

Consumer chains are run on infrastructure (virtual or physical machines) distinct from the provider, have their own configurations and operating requirements.

## What happens to consumer if provider is down?

In case the provider chain halts or experiences difficulties the consumer chain will keep operating - the provider chain and consumer chains represent different networks, which only share the validator set.

The consumer chain will not halt if the provider halts because they represent distinct networks and distinct infrastructures. Provider chain liveness does not impact consumer chain liveness.

However, if the `trusting_period` (currently 5 days for protocol safety reasons) elapses without receiving any updates from the provider, the consumer chain will essentially transition to a Proof of Authority chain.
This means that the validator set on the consumer will be the last validator set of the provider that the consumer knows about.

Steps to recover from this scenario and steps to "release" the validators from their duties will be specified at a later point.
At the very least, the consumer chain could replace the validator set, remove the ICS module and perform a genesis restart. The impact of this on the IBC clients and connections is currently under careful consideration.

## What happens to provider if consumer is down?

Consumer chains do not impact the provider chain.
The ICS protocol is concerned only with validator set management and the only communication that the provider requires from the consumer is information about validator activity (essentially keeping the provider informed about slash events).

## Can I run the provider and consumer chains on the same machine?

Yes, but you should favor running them in separate environments so failure of one machine does not impact your whole operation.

## Can the consumer chain have its own token?

As any other cosmos-sdk chain the consumer chain can issue its own token, manage inflation parameters and use them to pay gas fees.

## How are Tx fees paid on consumer?

The consumer chain operates as any other cosmos-sdk chain. The ICS protocol does not impact the normal chain operations.

## Are there any restrictions the consumer chains need to abide by?

No. Consumer chains are free to choose how they wish to operate, which modules to include, use CosmWASM in a permissioned or a permissionless way.
The only thing that separates consumer chains from standalone chains is that they share their validator set with the provider chain.

## What's in it for the validators and stakers?

The consumer chains sends a portion of its fees and inflation as reward to the provider chain as defined by `ConsumerRedistributionFraction`. The rewards are distributed (sent to the provider) every `BlocksPerDistributionTransmission`.

:::note
  `ConsumerRedistributionFraction` and `BlocksPerDistributionTransmission` are parameters defined in the `ConsumerAdditionProposal` used to create the consumer chain. These parameters can be changed via consumer chain governance.
:::

## Can the consumer chain have its own governance?

**Yes.**

In that case the validators are not necessarily part of the governance structure. Instead, their place in governance is replaced by "representatives" (governors). The representatives do not need to run validators, they simply represent the interests of a particular interest group on the consumer chain.

Validators can also be representatives but representatives are not required to run validator nodes.

This feature discerns between validator operators (infrastructure) and governance representatives which further democratizes the ecosystem. This also reduces the pressure on validators to be involved in on-chain governance.

## Can validators opt out of validating a consumer chain?

A validator can always opt out from an Opt-In consumer chain.
A validator can only opt out from a Top N chain if the validator does not belong to the top N% validators.

## How does Slashing work?

Validators that perform an equivocation or a light-client attack on a consumer chain are slashed on the provider chain.
We achieve this by submitting the proof of the equivocation or the light-client attack to the provider chain (see [slashing](features/slashing.md)).

## Can Consumer Chains perform Software Upgrades?

Consumer chains are standalone chains, in the sense that they can run arbitrary logic and use any modules they want (ie CosmWASM).

Consumer chain upgrades are unlikely to impact the provider chain, as long as there are no changes to the ICS module.

## How can I connect to the testnets?

Check out the [Joining Replicated Security testnet](./validators/joining-testnet.md) section.

## How do I start using ICS?

To become a consumer chain use this [checklist](./consumer-development/onboarding.md) and check the [App integration section](./consumer-development/app-integration.md)

## Which relayers are supported?

Currently supported versions:

- Hermes 1.4.1

## How does key delegation work in ICS?

You can check the [Key Assignment Guide](./features/key-assignment.md) for specific instructions.

## How does Partial Set Security work?

Partial Set Security allows a provider chain to share only a subset of its validator set with a consumer chain. This subset can be determined by the top N% validators by voting power, or by validators opting in to validate the consumer chain. Partial Set Security allows for flexible tradeoffs between security, decentralization, and the budget a consumer chain spends on rewards to validators.

See the [Partial Set Security](./features/partial-set-security.md) section for more information.

## How does a validator know which consumers chains it has to validate?

In order for a validator to keep track of all the chains it has to validate, the validator can use the
[`has-to-validate` query](validators/partial-set-security-for-validators.md#which-chains-does-a-validator-have-to-validate).

## How many chains can a validator opt in to?

There is **no** limit in the number of consumers chains a validator can choose to opt in to.

## Can validators assign a consensus keys while a consumer-addition proposal is in voting period?
Yes, see the [Key Assignment Guide](./features/key-assignment.md) for more information.

## Can validators assign a consensus key during the voting period for a consumer-addition proposal if they are not in the top N?
Yes.

## Can validators opt in to an Opt-in chain after its consumer-addition proposal voting period is over but before the spawn time?
Yes.

## Can validators opt in to an Opt-in chain after the spawn time if nobody else opted in?
No, the consumer chain will not be added if nobody opted in by the spawn time. At least one validator, regardless of its voting power, must opt in before the spawn time arrives in order for the chain can start.

## Can all validators opt out of an Opt-in chain?
Yes, the consumer chain will halt with an ERR CONSENSUS FAILURE error after the opt-out message for the last validator is received.

## Can validators set a commission rate for chains they have not opted in to?
Yes, and this is useful for validators that are not in the top N% of the provider chain, but might move into the top N% in the future.
By setting the commission rate ahead of time, they can make sure that they immediately have a commission rate of their choosing as soon as they are in the top N%.

## On how many consumer chains can a validator opt-in at the same time?

There is no limit to the number of consumer chains a validator can opt in to.
However, some consumer chains may restrict the validators actually getting to validate there, for example consumer chains can set up denylists to stop certain validators from validating there.
See the [Power Shaping](./features/power-shaping.md) section for more information. 
