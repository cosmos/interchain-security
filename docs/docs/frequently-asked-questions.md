---
sidebar_position: 6
title: "Frequently Asked Questions"
slug: /faq
---

## General

### What is Interchain Security (ICS)?

ICS is an IBC protocol that enables a provider chain (e.g., the Cosmos Hub) to provide security to multiple [consumer chains](#what-are-consumer-chains).
This means that consumer chains will leverage the stake locked on the provider chain for block production (i.e., a cross-chain proof-of-stake system). 
ICS allows anyone to launch a consumer chain using a subset, or even the entire, validator set from the provider chain.
Note that validators need to run separate infrastructure for the provider and consumer chains, resulting in different networks that only share (a subset of) the validator set.

### What is the difference between ICS and Partial Set Security (PSS)?

[ICS is a protocol](#what-is-interchain-security-ics). 
PSS is an ICS feature that allows a provider chain to share only a subset of its validator set with a consumer chain.
PSS differentiates between TopN and Opt-In consumer chains. 
For TopN chains, the validator subset is determined by the top N% provider validators by voting power.
For Opt-In chains, the validator subset is determined by validators opting in to validate the consumer chains. 
PSS allows for flexible tradeoffs between security, decentralization, and the budget a consumer chain spends on rewards to validators.

For more details, see the [PSS feature](./features/partial-set-security.md).

## Consumer Chains

### What are consumer chains?

Consumer chains are blockchains operated by (a subset of) the validators of the provider chain. 
The ICS protocol ensures that consumer chains get information about which validators should validate on them.
This information consists of the opted in validators and their power on the consumer chains.
Note that the validators' power on the consumer chains is a function of their stake locked on the provider chain.

Consumer chains are run on infrastructure (virtual or physical machines) distinct from the provider chain, have their own configurations and operating requirements.

Consumer chains are free to choose how they wish to operate and which modules to include. 
For example, they can choose to use CosmWasm either in a permissioned or a permissionless way.
Also, consumer chains are free to perform software upgrades at any time without impacting the provider chain.

### How to become a consumer chain?

To become a consumer chain use this [checklist](./consumer-development/onboarding.md) and check the [App integration section](./consumer-development/app-integration.md).

### What happens to consumers if the provider is down?

In case the provider chain halts or experiences difficulties, the consumer chains will keep operating - the provider chain and consumer chains represent different networks that only share (a subset of) the validator set.
As the validators run separate infrastructure on these networks, **_the provider chain liveness does not impact the liveness of consumer chains_**.

Every consumer chain communicates with the provider chain via a CCV channel -- an IBC ordered channel.
If any of the packets sent over the CCV channel timeout (see the [CCVTimeoutPeriod param](./introduction/params.md#ccvtimeoutperiod)), then the channel is closed and, consequently, the consumer chain transitions to a Proof of Authority (PoA) chain. 
This means that the validator set on the consumer will no longer be updated with information from the provider. 

### What happens to provider if any of the consumers are down?

**_Consumer chains do not impact the livness of the provider chain._**
The ICS protocol is concerned only with validator set management, and the only communication that the provider requires from the consumer is information about validator activity (essentially keeping the provider informed about slash events).

### Can consumer chains have their own token?

As any other Cosmos SDK chains, **_consumer chains can issue their own token_** and manage inflation parameters. 
Note that the ICS protocol does not impact the transaction fee system on the consumer chains. 
This means consumer chains can use any token (including their own token) to pay gas fees.
For more details, see the [democracy modules](./features/democracy-modules.md#tokenomics).

### Can consumer chains have their own governance?

Yes. ICS allows consumer chains to **_separate governance from block production_**.
Validator operators (with their stake locked on the provider) are responsible for block production, while _representatives_ (aka governators, governors) are responsible for on-chain governance. 
For more details, see the [democracy modules](./features/democracy-modules.md).

### Can a consumer chain modify its power shaping parameters?

Yes, by issuing a [`ConsumerModificationProposal`](./features/proposals.md#consumermodificationproposal).

### Can a Top N consumer chain become Opt-In or vice versa? 

Yes, by issuing a [`ConsumerModificationProposal`](./features/proposals.md#consumermodificationproposal).

## Validators

### How can validators opt in to validate a consumer chain?

Check the [validator guide to Partial Set Security](./validators/partial-set-security-for-validators.md#how-to-opt-in-to-a-consumer-chain).

An important note is that validator the top N% of the provider chain validator set are automatically opted in on Top N consumer chains. 

### Can validators opt in to an Opt-in chain after the spawn time if nobody else opted in?

No, the consumer chain will be removed if nobody opted in by the spawn time. At least one validator, regardless of its voting power, must opt in before the spawn time in order for the chain can start.

### How does a validator know which consumers chains it has to validate?

In order for a validator to keep track of all the chains it has to validate, the validator can use the
[`has-to-validate` query](./validators/partial-set-security-for-validators.md#which-chains-does-a-validator-have-to-validate).

### How many chains can a validator opt in to?

There is **no** limit in the number of consumers chains a validator can choose to opt in to.

### How can validators assign consumer keys?

Check the [Key Assignment guide](./features/key-assignment.md) for specific instructions.

Validators are strongly recommended to assign a separate key for each consumer chain and **not** reuse the provider key across consumer chains for security reasons.

Also note that validators can assign consensus keys before a consumer chain is launched (e.g., during the voting period for Top N consumer chains).

### What are the benefits for validators running consumer chains?

The consumer chains sends a portion of its block rewards (e.g., transaction fees and inflation) to the provider chain as defined by the [ConsumerRedistributionFraction param](./introduction/params.md#consumerredistributionfraction). 
These rewards are sent periodically to the provider (via IBC transfers), where they are distributed **ONLY** to the _opted in_ validators and their delegators. For more details, see the [Reward Distribution feature](./features/reward-distribution.md).

### Can validators set per consumer chain commission rates?

Yes. See the [validator guide to Partial Set Security](./validators/partial-set-security-for-validators.md#how-to-set-specific-per-consumer-chain-commission-rate).

### What are the risks for validators running consumer chains?

Validators that perform an equivocation or a light-client attack on a consumer chain are slashed on the provider chain. This is done by submitting a proof of the equivocation or the light-client attack to the provider chain.

In addition, consumer chains send IBC packets via the CCV channels informing the provider when opted in validators should be jailed for downtime. 
It is important to notice that _validators are not slashed for downtime on consumer chains_. 
The downtime logic is custom to the consumer chain. 
For example, Cosmos SDK chains can use the [slashing module](https://docs.cosmos.network/v0.50/build/modules/slashing) to configure the downtime window. 

For more details, see the [slashing feature](features/slashing.md).

### Can validators run the provider and consumer chains on the same machine?

In theory yes. 
In practice, we recommend validators to run the provider and consumer chains in separate environments for fault containment, i.e., failures of one machine do not impact the entire system.

### Can validators opt out of validating a consumer chain?

Validators can always opt out from an Opt-In consumer chain.
Validators can only opt out from a TopN chain if they do not belong to the top N% validators.

### Can all validators opt out of an Opt-in chain?

Note that if all validators opt out of an Opt-In consumer chain, then the chain will halt with a consensus failure upon receiving the `VSCPacket` with an empty validator set.

### How to connect to the testnets?

Check out the [Joining Interchain Security testnet](./validators/joining-testnet.md) section.

## Integrators 

### Which relayers are supported?

Currently supported versions:

- Hermes `v1.8.0+`

### How to check when the next validator update will be sent to the consumer chains?

Validator updates are sent to consumer chains every `BlocksPerEpoch` blocks.
Depending on the status of relayers between the Hub and the consumer chains,
it might take a while for the validator updates to be processed and applied on the consumer chains.

To query how many blocks are left until the next epoch starts,
run the following command:
```bash
interchain-security-pd query provider blocks-until-next-epoch
```
