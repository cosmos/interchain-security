---
sidebar_position: 2
title: ADR Template
---
# ADR 004: Denom DOS fixes

## Changelog
* 5/9/2023: ADR created

## Status

Accepted

## Context

The provider and consumer modules are vulnerable to similar issues involving an attacker sending millions of denoms to certain addresses and causing the chain to halt. This ADR outlines both fixes since they are similar. Both fixes involve processing only denoms that are on a whitelist to avoid iterating over millions of junk denoms but have different requirements and are implemented in different ways.

## Decision

### Provider

- Put the distribution module's FeePoolAddress back on the blocklist so that it cannot receive funds from users.
- Create a new address called ConsumerRewardPool and unblock it, allowing funds to be sent to it.
- Create a set of strings in the store for allowed ConsumerRewardDenoms.
- Create an endpoint called RegisterConsumerRewardDenom which deducts a fee from the sender's account, sends it to the community pool and adds a string to the ConsumerRewardDenoms set.
- Create a parameter called ConsumerRewardDenomRegistrationFee which determines the fee which is charged to register a consumer reward denom in the step above.
- Create a function called TransferRewardsToFeeCollector which gets the entire ConsumerRewardDenoms set from the store, iterates over it, and for each entry:
  - Gets the balance of this denom for the ConsumerRewardPool account
  - Sends the entire balance out to the FeePoolAddress using SendCoinsFromModuleToModule which is not affected by the blocklist.
- Run TransferRewardsToFeeCollector in the endblock
  
Now, nobody can send millions of junk denoms to the FeePoolAddress because it is on the block list. If they send millions of junk denoms to the ConsumerRewardPool, this does not matter because all balances are not iterated over, only those which are in the ConsumerRewardDenoms set.

We also add a new tx: register-consumer-reward-denom, and a new query: registered-consumer-reward-denoms

### Consumer

- Create a new param RewardDenoms with a list of strings
- Create a new param ProviderRewardDenoms with a list of strings
- Create a function AllowedRewardDenoms which iterates over ProviderRewardDenoms and converts each denom to its ibc-prefixed denom using the provider chain's ibc channel information, then concatenates the RewardDenoms list and returns the combined list of allowed denoms.
- In SendRewardsToProvider, instead of iterating over the balances of all denoms in the ToSendToProvider address, iterate over AllowedRewardDenoms

Now, if somebody sends millions of junk denoms to ToSendToProvider, they will not be iterated over. Only the RewardDenoms and ProviderRewardDenoms will be iterated over. Since we do not require this feature to be permissionless on the consumer, the registration fee process is not needed.

## Consequences

### Positive

- Denom DOS is no longer possible on either provider or consumer.

### Negative

- Consumer chain teams must pay a fee to register a denom for distribution on the provider, and add some extra parameters in their genesis file.
