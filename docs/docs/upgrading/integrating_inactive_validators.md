---
sidebar_position: 2
---

# Inactive Validators Integration Guide

With the [inactive validators feature of Interchain Security](../adrs/adr-017-allowing-inactive-validators.md), validators outside of the active set on the provider chain can validate on consumer chains that allow this. Technically, this is achieved by *increasing* the MaxValidators paramater in the staking module, to let additional validators be part of the set of bonded validators. However, to keep the set of validators participating in consensus on the Cosmos Hub the same, we introduce the MaxProviderConsensusValidators parameter in the provider module, which will restrict the number of validators that actively validate on the provider chain.

To clarify the terminology:

*bonded* validators are all validators that are bonded on the Cosmos Hub, and

*active* validators are all validators that actively participate in consensus on the Cosmos Hub.

Before the introduction of the feature, these two terms were equivalent: every bonded validator was active, and every active validator was bonded. *After* the introduction of this feature, it still holds that every active validator is bonded, but not every bonded validator is active.

Importantly, only *active* validators receive inflation rewards from ATOM; only *active* validators may vote on behalf of their delegators in governance, and *only active* validators can get slashed for downtime (because only those validators participate in consensus and produce blocks). Apart from these differences, *bonded but inactive* validators are just like *active* validators - they can receive delegations, and they can validate on consumer chains (and receive rewards for this) just like active validators.

The following queries will change after this upgrade:

* `/cosmos/staking/v1beta1/pool` / `gaiad query staking pool`

The `bonded_tokens` will include the stake of all *bonded* validators. As the number of bonded validators will be increased as part of the upgrade, the number of `bonded_tokens` is expected to have a sudden increase after the upgrade is applied.

* All queries in the staking module that return a `Validator`

All *bonded* validators will show with `Status=Bonded` . To identify *active* validators, query the validator set from Tendermint (https://docs.cometbft.com/v0.37/rpc/#/Info/validators or `query comet-validator-set [height]`), which will return the set of all *active* validators.