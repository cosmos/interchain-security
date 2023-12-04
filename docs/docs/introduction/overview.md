---
sidebar_position: 1
---

# Overview
:::info
Replicated security (aka interchain security V1) is an open sourced IBC application which allows cosmos blockchains to lease their proof-of-stake security to one another.
<br></br>
Replicated security allows anyone to launch a "consumer" blockchain using the same validator set as the "provider" blockchain by creating a governance proposal. If the proposal is accepted, provider chain validators start validating the consumer chain as well. Consumer chains will therefore inherit the full security and decentralization of the provider.
:::
## Why Replicated Security?

- Full provider security. At launch, consumer chains are secured by the full validator set and market cap of the provider chain.
- Independent block-space. Transactions on consumer chains do not compete with any other applications. This means that there will be no unexpected congestion, and performance will generally be much better than on a shared smart contract platform such as Ethereum.
- Projects keep majority of gas fees. Depending on configuration, these fees either go to the project’s community DAO, or can be used in the protocol in other ways.
- No validator search. Consumer chains do not have their own validator sets, and so do not need to find validators one by one. A governance vote will take place for a chain to get adopted by the provider validators which will encourage participation and signal strong buy-in into the project's long-term success.
- Instant sovereignty. Consumers can run arbitrary app logic similar to standalone chains. At any time in the future, a consumer chain can elect to become a completely standalone chain, with its own validator set.

## Core protocol

:::info
Protocol specification is available as [ICS-028](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md) in the IBC repository.
:::

Once an IBC connection and proper channel is established between a provider and consumer chain, the provider will continually send validator set updates to the consumer over IBC. The consumer uses these validator set updates to update its own validator set in Comet. Thus, the provider validator set is effectively replicated on the consumer.

To ensure the security of the consumer chain, provider delegators cannot unbond their tokens until the unbonding periods of each consumer chain has passed. In practice this will not be noticeable to the provider delegators, since consumer chains will be configured to have a slightly shorter unbonding period than the provider.

### Downtime Slashing

If downtime is initiated by a validator on a consumer chain, a downtime packet will be relayed to the provider to jail that validator for a set amount of time. The validator who committed downtime will then miss out on staking rewards for the configured jailing period.

### Tokenomics and Rewards

Consumer chains are free to create their own native token which can be used for fees, and can be created on the consumer chain in the form of inflationary rewards. These rewards can be used to incentivize user behavior, for example, LPing or staking. A portion of these fees and rewards will be sent to provider chain stakers, but that proportion is completely customizable by the developers, and subject to governance.

