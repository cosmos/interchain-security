---
sidebar_position: 14
title: ADR Template
---
# ADR 013: Slashing on the provider for consumer equivocation

## Changelog
* 1st Sept. 2023: Initial draft

## Status
Proposed

## Context
We present some approaches on how we can slash a validator on the provider chain for
an equivocation performed on the consumer chain. Currently, we can receive [evidence of equivocation](https://github.com/cosmos/interchain-security/pull/1232), 
but we do not have functionality to slash the misbehaving validator on the provider chain.
In what follows, we first explain how slashing is performed in the case of a single chain, to show why slashing on
the provider chain for a consumer equivocation is a challenging problem.

### Single-chain slashing
Slashing is implemented across the [slashing](https://docs.cosmos.network/v0.50/modules/slashing)
and [staking](https://docs.cosmos.network/v0.50/modules/staking#msgcreatevalidator-1)
modules. 
The slashing module’s [keeper.go](https://github.com/cosmos/cosmos-sdk/blob/5621d9d80736d6025c0f73263947e543fe88793f/x/slashing/keeper/keeper.go#L1) simply
calls
the staking module’s [Slash](https://github.com/cosmos/cosmos-sdk/blob/5621d9d80736d6025c0f73263947e543fe88793f/x/staking/keeper/slash.go#L37) with 
among others, the `infractionHeight` (i.e., height at which the equivocation occurred), the validator’s `power`, and
the `slashFactor` (5% in case of equivocation in Cosmos Hub -- see `gaiad query slashing params`).

#### Slashing undelegations and redelegations
To slash undelegations, [Slash](https://github.com/cosmos/cosmos-sdk/blob/bf249162e42ef084668b942e12538cb30f9e4846/x/staking/keeper/slash.go#L109)
goes through all undelegations and [checks](https://github.com/cosmos/cosmos-sdk/blob/bf249162e42ef084668b942e12538cb30f9e4846/x/staking/keeper/slash.go#L236)
on whether the undelegation started before or after the infraction. If the undelegation started before the `infractionHeight`
this undelegation is **not** slashed, otherwise the undelegation is [slashed](https://github.com/cosmos/cosmos-sdk/blob/bf249162e42ef084668b942e12538cb30f9e4846/x/staking/keeper/slash.go#L262) by
`slashFactor`.

The slashing of redelegations happens in a similar way, meaning that `Slash` goes through all redelegations and checks on whether
the redelegation started before or after the `infractionHeight`.

We believe that one of the "principles" behind using `infractionHeight` to decide on whether to slash a delegation or redelegation
has to do with the fact that we want to slash only delegators whose voting power _contributed_ to the infraction.
However, this is a rather obscure idea because a delegator `D` could start unbonding at height `H` and then a validator
could perform an equivocation before `H` intentionally. In such a case `D` would still get slashed, even though `D`
did not contribute any voting power per se for the equivocation. Furthermore, this principle is not respected in general
(see "Slashing delegations").

#### Slashing delegations
Besides undelegations and redelegations, we need to slash simple delegations on the validator.
This is performed by [deducting the appropriate amount of tokens](https://github.com/cosmos/cosmos-sdk/blob/5ca405ae067e7d8df98699f675e060f70a549976/x/staking/keeper/slash.go#L165)
from the validator. Note that this deduction is computed based on the voting `power` the misbehaving validator
had at the time of the infraction. As a result of the tokens deduction, 
the [tokens per share](https://docs.cosmos.network/v0.46/modules/staking/01_state.html#delegator-shares)
reduce and hence later on, when delegators undelegate or redelegate, the delegators retrieve back less
tokens, effectively having their tokens slashed. This approach of slashing delegations does not utilize the
`infractionHeight` in any way and hence the following could occur:
  1. a validator `V` performs an equivocation at a height `Hi`
  2. a new delegator `D` delegates to `V` after height `Hi`
  3. we receive the evidence of the equivocation by validator `V`
  4. we slash the tokens of delegator `D`
In the above scenario, delegator `D` is slashed, even though `D`'s voting power did not contribute to the infraction. 


#### Old evidence
In the single-chain case, we never receive old evidence (e.g., from 3 years ago). This is achieved through
[CometBFT](https://docs.cometbft.com/v0.37/spec/consensus/evidence) that filters old evidence based on the parameters
`MaxAgeNumBlocks` and `MaxAgeDuration` (see [here](https://github.com/cometbft/cometbft/blob/ae9826ed75ee411c0d809797ce209ee770c15c4f/evidence/pool.go#L266)).
In Cosmos Hub, the `MaxAgeNumBlocks` is set to 1000000 (i.e., ~70 days if we assume we need ~6 sec per block) and `MaxAgeDuration`
is set to 172800000000000 ns (i.e., 2 days). Because of this check, we can easily exclude old evidence.


###  Slashing on the provider
We see that in the single-chain slashing case, we use the `infractionHeight` and the voting `power` to be able to slash.
In order to slash the provider chain for a consumer chain infraction we need to have the provider's `infractionHeight`
and voting `power`. However, we do **not** have those values. We only have the `infractionHeight` in the consumer chain,
but we do not know to what provider height it corresponds. Unless we have a way to find the corresponding `infractionHeight`
and `power` in the provider chain, we cannot slash as we slash in the single-chain case. 

Additionally, we make the assumption that the consumer chain could be _malicious_ and hence we cannot trust any 
height-to-height correspondence it might inform us about.

This message could be sent through a relayer ... 
Note that when we receive evidence through a [MsgSubmitConsumerDoubleVoting](https://github.com/cosmos/interchain-security/pull/1232/files) message,
 we get what is contained in the [DuplicateVoteEvidence](https://github.com/cometbft/cometbft/blob/ae9826ed75ee411c0d809797ce209ee770c15c4f/types/evidence.go#L36):
```protobuf
type DuplicateVoteEvidence struct {
	VoteA *Vote `json:"vote_a"`
	VoteB *Vote `json:"vote_b"`

	// abci specific information
	TotalVotingPower int64
	ValidatorPower   int64
	Timestamp        time.Time
}
```
Note that the "abci specific information" is not useful because they are not signed and hence could be anything. Therefore,
we cannot use the `validatorPower` in any way in our slashing in the provider chain. We can get the `infractionHeight`
from the votes but this corresponds to the infraction height on the consumer chain. Furthermore, note that the 
[Timestamp](https://github.com/cometbft/cometbft/blob/ae9826ed75ee411c0d809797ce209ee770c15c4f/types/vote.go#L55) in the votes
is just the [BFT time](https://github.com/cometbft/cometbft/blob/main/spec/consensus/bft-time.md), and it could be anything
since a misbehaving validator could have included any time in it.

#### Clock drift between the provider and the consumer chain
(Still thinking on this but adding here as a first pointer to some ideas)
Conceptually, we have 2 different chains and there’s no guarantee that the clock drift betweeen them is bounded.
One could have BFT time of 2023 and the other from 2013. Having said this however, the chains communicate over IBC and
hence some timing constraints are imposed by IBC otherwise the chains could not communicate. IBC clients contain a 
`maxClockDrift` parameter but this is [only used](https://github.com/tendermint/tendermint/blob/ded310093e0d771c9ed27f296921cb6b23d99f29/light/verifier.go#L253-L256)
to reject headers that come slightly from the future. For example, if we assume `maxClockDrift` is 10 seconds in the
light client of a chain `A` and chain `A` has latest block time `12:58:31` and then `A` gets a header for one of its
light clients that has time `12:58:42` that is 11 seconds later, then this client update would get rejected by chain A.
However, even with this constraint we still do not know the real time of the chain `B` it could be 5 years ahead 

`trustingPeriod` only tells us from the provider side that we have received a message from the other chain in the
last `trustingPeriod` (2 weeks in Cosmos Hub) before ... so doesn't add much either ... 

We currently investigate on whether we can bound the clock drift between the provider and the consumer chain.

## Proposed solution
As a first iteration, in order to implement the slashing functionality as soon as possible, we propose an aggressive (i.e.,
would slash more delegators than in the single-chain case) slashing  approach because this allows for a straight-forward implementation.
In this approach, at the moment we receive evidence, at _evidence height_, we:
1. slash all the undelegations and redelegations using the `slashFactor`;
2. slash all delegations using as voting `power` the sum of the voting power of the misbehaving validator and the 
power of all the ongoing undelegations and redelegations.

**Evidence expiration:** Additionally, in this approach and because of what we explain earlier, because we cannot infer
the actual time the evidence was created in comparison to the provider's time, we we do not consider _evidence expiration_
and hence we can receive evidence from a time in the past (e.g., 3 years ago). As mentioned the timestamp inside a vote could contain
anything.

### Implementation
The aggressive approach allows for multiple simplifications. Specifically, we can introduce the following snippet 
in the [HandleConsumerDoubleVoting(](https://github.com/cosmos/interchain-security/pull/1232) method:
```go
undelegationsTotalAmount := sdk.NewInt(0)
for _, v := range k.stakingKeeper.GetUnbondingDelegationsFromValidator(ctx, validatorAddress) {
    for _, entry := range v.Entries {
        undelegationsTotalAmount = undelegationsTotalAmount.Add(entry.InitialBalance)
    }
}

redelegationsTotalAmount := sdk.NewInt(0)
for _, v := range k.stakingKeeper.GetRedelegationsFromSrcValidator(ctx, validatorAddress) {
    for _, entry := range v.Entries {
        redelegationsTotalAmount = redelegationsTotalAmount.Add(entry.InitialBalance)
    }
}

infractionHeight := 0
totalPower := validators voting Power + undelegationsTotalAmount.Add(redelegationsTotalAmount)
slashFraction := k.slashingKeeper.SlashFractionDoubleSign(ctx)

k.stakingKeeper.Slash(ctx, validatorConsAddress, infractionHeight, totalPower, slashFraction, DoubleSign)
```

**Infraction height:** We provide `infractionHeight` to the [Slash](https://github.com/cosmos/cosmos-sdk/blob/5621d9d80736d6025c0f73263947e543fe88793f/x/staking/keeper/slash.go#L37)
method to slash all ongoing undelegations and redelegations. 

**Power:** We pass the sum of the voting power of the misbehaving validator and the
power of all the ongoing undelegations and redelegations. This is a slightly more aggressive approach than just providing
the voting `power` at the evidence height. If we assume that the `slashFactor` is 5%, then the `power` we would pass
would be `validatorPower + 0.05 * totalPower(undelegations) + 0.05 * totalPower(redelegations)`. Hence when the `Slash`
method slashes all the undelegations and redelegations it would end up with 
`validatorPower + 0.05 * totalPower(undelegations) + 0.05 * totalPower(redelegations) - 0.05 * totalPower(undelegations) - 0.05 * totalPower(redelegations) = validatorPower`
and hence it would slash 5% of the `validatorPower` at evidence height.

**Storing evidence:** As mentioned, we do not expire evidence in this approach. However, because we do not want to
slash the same validator more than once for the same infraction, we have to store the evidence in some _cache_ in order
to check if we have already slashed based on received evidence. We could do the following:

```go

key := hashEvidence(dve DuplicateVoteEvidence) // would only use the signed VoteA and VoteB to generate the hash from the evidence

if key not in cache {
	store (key, validatorAddr) in cache
	perform slashing
} else {
	// do not slash
}
```
To prevent this cache from growing arbitrarily big, we can introduce some additional checks. For example, if the evidence
is for a validator that is not in the active validator set we can skip from storing it in the cache, etc.
Cleaning up of the cache could also be periodically performed by checking if the validator `validatorAddr` of a cache entry
is still in the active set, if not we remove that entry from the cache.

### Positive
With the proposed approach we can quickly implement slashing functionality for consumer chains on the provider chain.
This approach does not need any changes in the `staking` module and therefore does not change in any way how slashing is performed
today for a single chain.

### Negative
We _definitely_ slash more when it comes to undelegations and redelegations because we slash all of them.
We _potentially_ slash more than what we would have slashed if we knew the corresponding `votingPower` in the provider 
chain.

### Neutral



## Can we expire the evidence?
This is orthogonal to the above solution and describes a way to check whether evidence has expired or not.
Lamport clocks.


## References

> Are there any relevant PR comments, issues that led up to this, or articles referenced for why we made the given design choice? If so link them here!

* {reference link}
