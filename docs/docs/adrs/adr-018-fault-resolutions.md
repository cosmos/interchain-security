---
sidebar_position: 18
title: ADR Fault Resolutions
---
# ADR 018: Fault Resolutions

## Changelog
* 17th July 2024: Initial draft

## Status

Proposed

## Context

Partial Set Security ([PSS](./adr-015-partial-set-security.md)) allows a subset of a provider chain's validator set to secure a consumer chain.
 While this shared security scheme has many advantages, it comes with a risk known as the
 [subset problem](https://informal.systems/blog/replicated-vs-mesh-security#risks-of-opt-in-security-also-known-as-ics-v-2).
 This problem arises when a malicious majority of validators from the provider chain collude and misbehave on a consumer chain.
 This threat is particularly relevant for Opt-in chains since they might be secured by a relatively small subset of the provider's validator set.  

In cases of collusion, various types of misbehaviour can be performed by the validators, such as:

* Incorrect executions to break protocol rules in order to steal funds.
* Liveness attacks to halt the chain or censor transactions.
* Oracle attacks to falsify information used by the chain logic.

Currently, these types of attacks aren't handled in PSS, leaving the malicious validators unpunished.

A potential solution is to use fraud proofs. This technology allows proving incorrect state transitions of a chain without a full node.
 However, this is a complex technology, and there is no framework that works for Cosmos chains to this day.


To address this risk in PSS, a governance-gated slashing solution can be used until fraud proof technology matures.


This ADR proposes a fault resolution mechanism, which is a type of governance proposal that victims of faults can use to vote on the
 slashing of validators that misbehave on Opt-in consumer chains.

In what follows, we describe the implementation of a fault resolution mechanism that handles incorrect executions on consumer chains,
 as a first iteration.


## Decision

The proposed solution introduces a new `consumer-fault-resolution` governance proposal type to the `provider` module, which allows
 validators to be penalised for committing faults on an Opt-in consumer chain.

If such a proposal passes, the proposal handler tombstones all the validators listed in the proposal and slashes them by a predefined
 amount or the default value used for double-sign infractions.

The proposal has the following fields:

- **Description**: This field should be filled with a fault definition describing the type of misbehavior that the validators executed
 on an Opt-in consumer chain. A fault definition should precisely describe how an attack was performed and why it is eligible as a slashable fault.
- **Consumer Chain**: The chain that the fault was related to.
- **Validators**: The list of all the validators to be slashed.

In addition, in order to prevent spamming, users are required to pay a fee of `100ATOM` to submit a fault resolution to the provider.

### Validations

The submission of a fault resolution fails if any of the following conditions are not met:

- the consumer chain is an Opt-in chain
- all listed validators were opted-in to the consumer chain in the past unbonding-period
- the `100ATOM` fee is provided

### Additional considerations

Fault resolution proposals should be `expedited`  to minimize the time given to the listed validators to
to unbond to avoid punishment (see [Expedited Proposals](https://docs.cosmos.network/v0.50/build/modules/gov#expedited-proposals)) .


## Consequences

### Positive

- Provide the ability to slash and tombstone validators for committing incorrect executions on Opt-in consumer chains.

### Negative

- Assuming that malicious validators unbond immediately after misbehaving, a fault resolution has to be submitted within a maximum
 of two weeks in order to slash the validators.

### Neutral

- Fault definitions need to have a clear framework in order to avoid debates about whether an attack has actually taken place.  

## References

 <!-- TODO: add Fault Resolution CHIPs discussion here when it's published -->

* [Enabling Opt-in and Mesh Security with Fraud Votes](https://forum.cosmos.network/t/enabling-opt-in-and-mesh-security-with-fraud-votes/10901)

* [CHIPs discussion phase: Partial Set Security](https://forum.cosmos.network/t/chips-discussion-phase-partial-set-security-updated/11775)

* [Replicated vs. Mesh Security](https://informal.systems/blog/replicated-vs-mesh-security#risks-of-opt-in-security-also-known-as-ics-v-2)



