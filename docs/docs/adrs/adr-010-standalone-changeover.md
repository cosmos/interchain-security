---
sidebar_position: 11
title: Standalone to Consumer Changeover
---
## ADR 010: Standalone to Consumer Changeover

## Changelog

* 6/30/23: Feature completed, first draft of ADR.

## Status

Implemented

## Context

[Stride](https://github.com/Stride-Labs/stride) will be the first consumer to "changeover" from a standalone cosmos blockchain, to a consumer chain secured by the Cosmos Hub. This document will outline the changes made to the replicated security protocol to support this changeover process.

## Decision

### Process

Prior to the changeover, the consumer chain will have an existing staking keeper and validator set, these may be referred to as the "standalone staking keeper" and "standalone validator set" respectively.  

The first step in the changeover process is to submit a ConsumerAdditionProposal. If the proposal passes, the provider will create a new IBC client for the consumer at spawn time, with the provider's validator set. A consumer genesis will also be constructed by the provider for validators to query. Within this consumer genesis contains the initial validator set for the consumer to apply after the changeover.

Next, the standalone consumer chain runs an upgrade which adds the CCV module, and is properly setup to execute changeover logic.

The consumer upgrade height must be reached after the provider has created the new IBC client. Any replicated security validators who will run the consumer, but are not a part of the sovereign validator set, must sync up a full node before the consumer upgrade height is reached. The disc state of said full node will be used to run the consumer chain after the changeover has completed.

The meat of the changeover logic is that the consumer chain validator set is updated to that which was specified by the provider via the queried consumer genesis. Validators which were a part of the old set, but not the new set, are given zero voting power. Once these validator updates are given to Comet, the set is committed, and in effect 2 blocks later (see [FirstConsumerHeight](../../../x/ccv/consumer/keeper/changeover.go#L19)).

A relayer then establishes the new IBC connection between the provider and consumer. The CCV channel handshake is started on top of this connection. Once the CCV channel is established and VSC packets are being relayed, the consumer chain is secured by the provider.

### Changes to CCV Protocol

* Consumer Genesis state is updated to include a `PreCCV` boolean. When this boolean is set true in the  consumer genesis JSON, [special logic](../../../x/ccv/consumer/keeper/changeover.go) is executed on InitGenesis to trigger the changeover process on the consumer's first endblocker after the upgrade which adds the CCV module. Note that InitGenesis is not automatically called during chain upgrades, so the consumer must manually call the consumer's InitGenesis method in an upgrade handler.
* The `ConsumerAdditionProposal` type is updated to include a `DistributionTransmissionChannel` field. This field allows the consumer to use an existing IBC transfer channel to send rewards as a part of the CCV protocol. Consumers that're not changing over from a standalone chain will leave this field blank, indicating that a new transfer channel should be created on top of the same connection as the CCV channel.
* The CCV consumer keeper is updated to contain an optional reference to the standalone staking keeper. The standalone staking keeper is used to slash for infractions that happened before the changeover was completed. Ie. any infraction from a block height before the changeover, that is submitted after the changeover, will call the standalone staking keeper's slash method. Note that a changeover consumer's  standalone staking keeper becomes a democracy module keeper, so it is possible for a governance token to be slashed.

## Consequences

### Positive

* Existing cosmos chains are now able to onboard over to a consumer chain secured by a provider.
* The previous staking keepers for such chains can be transitioned to democracy staking module keepers.

### Negative

* The delineation between different types of consumers in this repo becomes less clear. Ie. there is code in the [democracy consumer's app.go](../../../app/consumer-democracy/app.go) that only applies to a previously standalone chain, but that file also serves as the base for a normal democracy consumer launched with RS from genesis.

## References

* EPIC: Standalone to Consumer Changeover [#756](https://github.com/cosmos/interchain-security/issues/756)
* [Changeover diagram from Stride](https://app.excalidraw.com/l/9UFOCMAZLAI/5EVLj0WJcwt)
