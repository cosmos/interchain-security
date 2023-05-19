---
sidebar_position: 2
---

# Consumer Chain Governance

Different consumer chains can do governance in different ways. However, no matter what the governance method is, there are a few settings specifically related to consensus that consumer chain governance cannot change. We'll cover what these are in the "Whitelist" section below.

## Democracy module

The democracy module provides a governance experience identical to what exists on a standalone Cosmos chain, with one small but important difference. On a standalone Cosmos chain validators can act as representatives for their delegators by voting with their stake, but only if the delegator themselves does not vote. This is a lightweight form of liquid democracy.

Using the democracy module on a consumer chain is the exact same experience, except for the fact that it is not the actual validator set of the chain (since it is a consumer chain, these are the Cosmos Hub validators) acting as representatives. Instead, there is a separate representative role who token holders can delegate to and who can perform the functions that validators do in Cosmos governance, without participating in proof of stake consensus.

For an example, see the [Democracy Consumer](https://github.com/octopus-network/interchain-security/tree/main/app/consumer-democracy)

## CosmWasm

There several great DAO and governance frameworks written as CosmWasm contracts. These can be used as the main governance system for a consumer chain. Actions triggered by the CosmWasm governance contracts are able to affect parameters and trigger actions on the consumer chain.

For an example, see [Neutron](https://github.com/neutron-org/neutron/).

## The Whitelist

Not everything on a consumer chain can be changed by the consumer's governance. Some settings having to do with consensus etc. can only be changed by the provider chain. Consumer chains include a whitelist of parameters that are allowed to be changed by the consumer chain governance. For an example, see [Neutron's](https://github.com/neutron-org/neutron/blob/main/app/proposals_allowlisting.go) whitelist.
