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
This ADR presents some approaches on how to slash on the provider chain validators that performed equivocations on consumer chains.
Currently, the provider chain can [receive and verify evidence of equivocation](https://github.com/cosmos/interchain-security/pull/1232), but it cannot slash the misbehaving validator.

In the remainder of this section, we explain how slashing is performed on a single chain and show why slashing on the provider for equivocation on the consumer is challenging.

Note that future versions of the Cosmos SDK and CometBFT could modify the way we slash, etc. Therefore, a future reader of this ADR, should note that when we refer to Cosmos SDK and CometBFT we specifically refer to their [v0.47](https://docs.cosmos.network/v0.47/intro/overview) and [v0.37](https://docs.cometbft.com/v0.37/) versions respectively.

### Single-chain slashing
Slashing is implemented across the [slashing](https://docs.cosmos.network/v0.47/modules/slashing)
and [staking](https://docs.cosmos.network/v0.47/modules/staking) modules. 
The slashing module's keeper calls the staking module's `Slash()` method, passing among others, the `infractionHeight` (i.e., the height when the equivocation occurred), the validator's `power` at the infraction height, and the `slashFactor` (currently set to `5%` in case of equivocation on the Cosmos Hub).

#### Slashing undelegations and redelegations
To slash undelegations, `Slash` goes through all undelegations and checks whether they started before or after the infraction occurred. If an undelegation started before the `infractionHeight`, then it is **not** slashed, otherwise it is slashed by `slashFactor`.

The slashing of redelegations happens in a similar way, meaning that `Slash` goes through all redelegations and checks whether the redelegations started before or after the `infractionHeight`.

#### Slashing delegations
Besides undelegations and redelegations, the validator's delegations need to also be slashed.
This is performed by deducting the appropriate amount of tokens from the validator. Note that this deduction is computed based on the voting `power` the misbehaving validator had at the height of the equivocation. As a result of the tokens deduction, 
the [tokens per share](https://docs.cosmos.network/v0.47/modules/staking#delegator-shares)
reduce and hence later on, when delegators undelegate or redelegate, the delegators retrieve back less
tokens, effectively having their tokens slashed. This approach of slashing delegations does not utilize the
`infractionHeight` in any way and hence the following scenario could occur:
  1. a validator `V` performs an equivocation at a height `Hi`
  2. a new delegator `D` delegates to `V` after height `Hi`
  3. evidence of the equivocation by validator `V` is received
  4. the tokens of delegator `D` are slashed

In the above scenario, delegator `D` is slashed, even though `D`'s voting power did not contribute to the infraction. 


#### Old evidence
In the single-chain case, old evidence (e.g., from 3 years ago) is ignored. This is achieved through 
[CometBFT](https://docs.cometbft.com/v0.37/spec/consensus/evidence) that ignores old evidence based on the parameters `MaxAgeNumBlocks` and `MaxAgeDuration` (see [here](https://github.com/cometbft/cometbft/blob/v0.37.0/evidence/pool.go#271)). 
Additionally, note that when the evidence is sent by CometBFT to the application, the evidence is rechecked in the [evidence module](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/evidence/keeper/infraction.go#L54) of Cosmos SDK and if it is old, the evidence is ignored. 
In Cosmos Hub, the `MaxAgeNumBlocks` is set to 1000000 (i.e., ~70 days if we assume we need ~6 sec per block) and `MaxAgeDuration` is set to 172800000000000 ns (i.e., 2 days). Because of this check, we can easily exclude old evidence.

###  Slashing on the provider
We see that in the single-chain slashing case, we use the `infractionHeight` and the voting `power` to be able to slash.
In order to slash the provider chain for a consumer chain equivocation we need to have the provider's `infractionHeight`
and voting `power`. However, we do **not** have those values. We only have the `infractionHeight` in the consumer chain
(that we can extract from the votes), but we do not know to what provider height this `infractionHeight` corresponds.
Unless we have a way to find the corresponding `infractionHeight`
and `power` in the provider chain, we cannot directly slash in the same way as we slash in the single-chain case. 

Someone might think that the problem of figuring out the corresponding `infractionHeight` and `power` values in 
the provider chain is easy because we could have the consumer chain send us this information. However, we 
consider that the application on the consumer chain could be _malicious_ and hence we
cannot really trust anything that stems from the _application state_ of the consumer chain. 

Note that when a relayer or a user sends evidence through a [MsgSubmitConsumerDoubleVoting](https://github.com/cosmos/interchain-security/pull/1232/files) message, we get what is contained in the [DuplicateVoteEvidence](https://github.com/cometbft/cometbft/blob/v0.37.0/types/evidence.go#L35):
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
The "abci specific information" cannot be trusted because they are not signed. Therefore,
we cannot use the `ValidatorPower` in any way for slashing in the provider chain. We can get the `infractionHeight`
from the votes but this corresponds to the infraction height on the consumer chain. Furthermore, note that the [Timestamp](https://github.com/cometbft/cometbft/blob/v0.37.0/types/vote.go#L55) in the votes is just the [BFT time](https://github.com/cometbft/cometbft/blob/v0.37.0/spec/consensus/bft-time.md), and the time could be anything since a misbehaving validator could have included any time in the votes.

Finally, note that in the single-chain case, we trust the underlying consensus engine (CometBFT) and hence when we receive
evidence from CometBFT we can act on it. In the case of provider and consumer chains however we cannot trust the evidence as is.



#### Clock drift between the provider and the consumer chain
(Still thinking on this but adding here as a first pointer to some ideas)

Conceptually, we have 2 different chains and there’s no guarantee that the clock drift between them is bounded.
One could have BFT time of 2023 on one chain and on the other chain a BFT time of 2013. 
Nevertheless, the chains communicate over IBC and
hence some timing constraints are imposed by IBC otherwise the chains could not communicate (e.g., light clients could expire).
IBC clients contain a `maxClockDrift` parameter but this is [only used](https://github.com/cometbft/cometbft/blob/v0.37.0/light/verifier.go#L176)
to reject headers that come slightly from the future. For example, assume a chain `A` that has a light client `lc` that 
tracks chain `B` and that has `maxClockDrift` of 10 seconds. If chain `A` has time `12:58:31` and
then `lc` receives a header with time `12:58:42` (that is 11 seconds from the future), then `lc` would reject his client update.
However, even with this `maxClockDrift` constraint we still do not know the time at the chain `B`, e.g., `B`'s BFT time could be 5 years ahead 
compared to chain's `A` BFT time.

(TODO: add more on the `trustingPeriod`) only tells us from the provider side that we have received a message from the other chain in the
last `trustingPeriod` (2 weeks in Cosmos Hub) before ... so doesn't add much either ... 

We currently investigate on whether we can bound the clock drift between the provider and the consumer chain.

## Proposed solution
As a first iteration, in order to implement the slashing functionality as soon as possible, we propose an aggressive (i.e.,
would slash more delegators than in the single-chain case) slashing  approach because this allows for a straight-forward implementation.
In this approach, at the moment we receive evidence, at _evidence height_, we:
1. slash all the undelegations and redelegations using the `slashFactor`;
2. slash all delegations using as voting `power` the sum of the voting power of the misbehaving validator and the 
power of all the ongoing undelegations and redelegations.

**Evidence expiration:** Additionally, in this approach and because of what we explained earlier, because at the moment
we cannot infer the actual time the evidence was created (i.e., timestamp in evidence could contain anything), we do not consider 
_evidence expiration_ and hence we can receive and act on evidence from a time in the past (e.g., 3 years ago).

### Implementation
The aggressive approach allows for multiple simplifications. Specifically, we can introduce the following snippet 
in the [HandleConsumerDoubleVoting](https://github.com/cosmos/interchain-security/pull/1232) method:
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

**Infraction height:** We provide a zero `infractionHeight` to the [Slash](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/staking/keeper/slash.go#L33) method in order to slash all ongoing undelegations and redelegations (see checks in [Slash](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/staking/keeper/slash.go#L92),
[SlashUnbondingDelegation](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/staking/keeper/slash.go#L195), and
[SlashRedelegation](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/staking/keeper/slash.go#L249)).

**Power:** We pass the sum of the voting power of the misbehaving validator and the
power of all the ongoing undelegations and redelegations. This is a slightly more aggressive approach than just providing
the voting `power` at the evidence height. If we assume that the `slashFactor` is 5%, then the `power` we pass
is `validatorPower + totalPower(undelegations) + totalPower(redelegations)`. Hence, when the `Slash`
method slashes all the undelegations and redelegations it would end up with 
`0.05 * validatorPower + 0.05 * totalPower(undelegations) + 0.05 * totalPower(redelegations) - 0.05 * totalPower(undelegations) - 0.05 * totalPower(redelegations) = 0.05 * validatorPower`
and hence it would slash 5% of the `validatorPower` at evidence height.

**Storing evidence:** As mentioned, we do not expire evidence with this aggresive approach. However, because we do not want to
slash the same validator more than once for the same infraction, we have to store the evidence in some _cache_ in order
to check if we have already slashed based on received evidence. We could do something similar to the following:

```go

// hashEvidence should only use the signed parts of the evidence to generate the hash
// therefore, it should only use VoteA and VoteB to avoid someone changing other parts DuplicateVoteEvidence
// and resubmitting
key := hashEvidence(dve DuplicateVoteEvidence) 

if key not in cache {
	store (key, validatorAddr) in cache
	perform slashing
} else {
	// do not slash
}
```
To prevent this cache from growing arbitrarily big, we can introduce some additional checks. For example, if the evidence
is for a validator that is not in the active validator set we can skip from storing it in the cache, etc.
We can also periodically clean up the cache by checking if the validator `validatorAddr` of a cache entry
is still in the active set and if not we remove that entry from the cache.

### Positive
With the proposed approach we can quickly implement slashing functionality on the provider chain for consumer chain equivocations.
This approach does not need any changes in the staking module and therefore does not change in any way how slashing is performed
today for a single chain.

### Negative
We _definitely_ slash more when it comes to undelegations and redelegations because we slash for all of them without
considering an `infractionHeight`.
We _potentially_ slash more than what we would have slashed if we knew the corresponding `votingPower` in the provider 
chain.



## Can we expire the evidence?
This is _orthogonal_ to the above solution and describes a way to check whether evidence has expired or not.

(TODO: Add Josef's idea on using Lamport clocks to expire old evidence.)



## References
* [feat: add handler for consumer double voting #1232](https://github.com/cosmos/interchain-security/pull/1232)
* [Cryptographic equivocation slashing design](https://forum.cosmos.network/t/cryptographic-equivocation-slashing-design/11400)
* [Update client may cause "new header has a time from the future" chain error #1445](https://github.com/informalsystems/hermes/issues/1445)
