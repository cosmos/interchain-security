---
sidebar_position: 1
---

# Overview

Interchain Security (ICS) is an open source IBC application that allows Cosmos chains to lease their proof-of-stake security to one another.

ICS allows anyone to launch a _consumer_ chain using a subset, or even the entire, validator set from the _provider_ chain by creating a governance proposal. If the proposal is accepted, provider chain validators start validating the consumer chain as well. Consumer chains will therefore inherit security and decentralization from the provider.

## Why Interchain Security?

- **Tailored security.** 
  Consumer chains can choose the right level of security based on their needs: 
  Chains can choose to inherit the whole validator set from the provider, or they can launch as an opt in chain with a subset of the provider validators. 
  Additionally, consumer chains have the power to shape the validator set to their specific requirements by setting allow & deny lists, capping its size, etc. 
  This allows for a wide range of security tradeoffs. 
  For example, it enables emerging projects to deploy on consumer chains that don’t need high level of security.
- **Separation of governance from block production.**
  Consumer chains can separate their governance mechanism from block production.
  Block production is handled by provider validators, which means it is an extension of the proof-of-state (PoS) mechanism on the provider chain.
  Governance on the consumer chains can rely on the same PoS mechanism (using the same stake locked on the provider), but it doesn't have to. 
  For example, consumer chains can have a governance system based on proof-of-authority (PoA) or on PoS using the consumer token (which would make the consumer token a governance token). 
  This also allows the governance to be more decentralized without affecting consensus (i.e., increasing the number of validators usually leads to slower block production). 
- **Distribution of block rewards.** 
  Consumer chains can choose how to distribute the block rewards (i.e., inflation and fees), what percentage to send to the provider as payment for block production, and what percentage to keep on-chain. 
  The rewards kept on-chain can then be distributed to the community DAO (the consumer's governance) or can be used in the protocol in other ways.
- **No validator search.** 
  Consumer chains do not have their own validator sets, and so do not need to find validators one by one. 
  Validators from the provider chain validate on the consumer chain with their stake on the provider chain, earning additional rewards. 
  For the consumer chain, this comes with the benefit of exposing their chain to the wider audience of the provider chain.
- **Instant sovereignty.** 
  Consumers can run arbitrary app logic similar to standalone chains. At any time in the future, a consumer chain can elect to become a completely standalone chain, with its own validator set.
- **Block-space sharding.** 
  Consumer chains are Cosmos appchains, which means that transactions on these chains do not compete with any other applications. As a result, there will be no unexpected congestion, and performance will generally be much better than on a shared smart contract platform such as Ethereum.

## Core protocol

**Validator updates**. 
Once an IBC connection and channel are established between a provider and consumer chain, the provider will continually send validator set updates to the consumer over IBC. Note the provider only sends updates for opted in validators. 
The consumer uses these validator set updates to update its own validator set in the consensus engine (e.g., CometBFT).

**Slashing and jailing.** 
If the opted-in validators misbehave on the consumer chains, then they will be punished on the provider chain. 
ICS currently differentiates between two type of infractions -- double signing and downtime. 
Double signing on consumer chains results in the misbehaving validators having their provider stake slashed and being permanently jailed on the provider, 
while downtime on consumer chains results in the misbehaving validators being temporarily jailed. 
Note that jailing entails removing the validator from the provider active validator set and, consequently, from any of the consumer validato sets. 
This entails the validator will miss out on both staking and ICS rewards. 

**Tokenomics and rewards.** 
Consumer chains are free to create their own native token which can be used for fees, and can be created on the consumer chain in the form of inflationary rewards. 
These rewards can be used to incentivize user behavior, for example, LPing or staking. 
A percentage of these fees and rewards will be sent to provider chain to be distributed among the opted in validators and their delegators. 
The percentage is completely customizable by the developers and subject to governance.

