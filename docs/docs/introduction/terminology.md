---
sidebar_position: 2
---

# Terminology

You may have heard of one or multiple buzzwords thrown around in the cosmos and wider crypto ecosystem such shared security, interchain security, replicated security, cross chain validation, and mesh security. These terms will be clarified below, before diving into any introductions.

## Shared Security

Shared security is a family of technologies that include optimistic rollups, zk-rollups, sharding and Interchain Security. Ie. any protocol or technology that can allow one blockchain to lend/share it's proof-of-stake security with another blockchain or off-chain process.

## Interchain Security

Interchain Security is the Cosmos-specific category of Shared Security that uses IBC (Inter-Blockchain Communication), i.e. any shared security protocol built with IBC.

## Replicated Security

A particular protocol/implementation of Interchain Security that fully replicates the security and decentralization of a validator set across multiple blockchains. Replicated security has also been referred to as "Cross Chain Validation" or "Interchain Security V1", a legacy term for the same protocol. That is, a "provider chain" such as the Cosmos Hub can share its exact validator set with multiple consumer chains by communicating changes in its validator set over IBC. Note this documentation is focused on explaining the concepts from replicated security.

## Mesh security

A protocol built on IBC that allows delegators on a cosmos chain to re-delegate their stake to validators in another chain's own validator set, using the original chain's token (which remains bonded on the original chain). For a deeper exploration of mesh security, see [Replicated vs. Mesh Security on the Informal Blog](https://informal.systems/blog/replicated-vs-mesh-security).

## Consumer Chain

Chain that is secured by the validator set of the provider, instead of its own.
Replicated security allows the provider chain validator set to validate blocks on the consumer chain.

## Sovereign Chain

Chain that is secured by its own validator set. This chain does not participate in replicated security.

## Changeover Procedure

Chains that were not initially launched as consumers of replicated security can still participate in the protocol and leverage the economic security of the provider chain. The process where a sovereign chain transitions to being a replicated consumer chain is called the **changeover procedure** and is part of the interchain security protocol. After the changeover, the new consumer chain will retain all existing state, including the IBC clients, connections and channels already established by the chain.
