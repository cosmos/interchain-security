---
sidebar_position: 14
title: Slashing on the provider for consumer equivocation
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

Note that future versions of the Cosmos SDK, CometBFT, and ibc-go could modify the way we slash, etc. Therefore, a future reader of this ADR, should note that when we refer to Cosmos SDK, CometBFT, and ibc-go we specifically refer to their [v0.47](https://docs.cosmos.network/v0.47/intro/overview),  [v0.37](https://docs.cometbft.com/v0.37/) and [v7.3.0](https://github.com/cosmos/ibc-go/blob/v7.3.0) versions respectively.

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
tokens, effectively having their tokens slashed. The rationale behind this slashing mechanism, as mentioned in the [Cosmos SDK documentation](https://docs.cosmos.network/v0.47/modules/staking#delegator-shares):
> [...] is to simplify the accounting around slashing. Rather than iteratively slashing the tokens of every delegation entry, instead the Validators total bonded tokens can be slashed, effectively reducing the value of each issued delegator share.

This approach of slashing delegations does not utilize the
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

###  Slashing for equivocation on the consumer
In the single-chain case, slashing requires both the `infractionHeight` and the voting `power`.
In order to slash on the provider for an equivocation on a consumer, we need to have both the provider's `infractionHeight` and voting `power`.
Note that the `infractionHeight` on the consumer chain must be mapped to a height on the provider chain.
Unless we have a way to find the corresponding `infractionHeight` and `power` on the provider chain, we cannot slash for equivocation on the consumer in the same way as we would slash in the single-chain case.


The challenge of figuring out the corresponding `infractionHeight` and `power` values on the provider chain is due to the following trust assumption:

- We trust the consensus layer and validator set of the consumer chains, _but we do not trust the application layer_.

As a result, we cannot trust anything that stems from the _application state_ of a consumer chain.

Note that when a relayer or a user sends evidence through a [MsgSubmitConsumerDoubleVoting](https://github.com/cosmos/interchain-security/pull/1232) message, the provider gets access to [DuplicateVoteEvidence](https://github.com/cometbft/cometbft/blob/v0.37.0/types/evidence.go#L35):
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
The "abci specific information" fields cannot be trusted because they are not signed. Therefore,
we can use neither `ValidatorPower` for slashing on the provider chain, nor the `Timestamp` to check the evidence age. We can get the `infractionHeight` from the votes, but this `infractionHeight` corresponds to the infraction height on the consumer and **not** on the provider chain.
Similarly, when a relayer or a user sends evidence through a [MsgSubmitConsumerMisbehaviour](https://github.com/cosmos/interchain-security/pull/826) message, the provider gets access to [Misbehaviour](https://github.com/cosmos/ibc-go/blob/v7.3.0/proto/ibc/lightclients/tendermint/v1/tendermint.proto#L79) that we cannot use to extract the infraction height, power, or the time on the provider chain.

## Proposed solution
As a first iteration, we propose the following approach. At the moment the provider receives evidence of equivocation on a consumer:
1. slash all the undelegations and redelegations using `slashFactor`;
2. slash all delegations using as voting `power` the sum of the voting power of the misbehaving validator and the power of all the ongoing undelegations and redelegations.

**Evidence expiration:** Additionally, because we cannot infer the actual time of the evidence (i.e., the timestamp of the evidence cannot be trusted), we do not consider _evidence expiration_ and hence old evidence is never ignored (e.g., the provider would act on 3 year-old evidence of equivocation on a consumer).
Additionally, we do not need to store equivocation evidence to avoid slashing a validator more than once, because we [do not slash](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/evidence/keeper/infraction.go#L94) tombstoned validators and we [tombstone](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/evidence/keeper/infraction.go#L138) a validator when slashed.

We do not act on evidence that was signed by a validator [consensus key](https://tutorials.cosmos.network/tutorials/9-path-to-prod/3-keys.html#what-validator-keys) that is _pruned_ when we receive the evidence. We prune a validator's consensus key if the validator has assigned a new consumer key (using `MsgAssignConsumerKey`) and an unbonding period on the consumer chain has elapsed (see [key assignment ADR](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-001-key-assignment.md)). Note that the provider chain is informed that the unbonding period has elapsed on the consumer when the provider receives a `VSCMaturedPacket` and because of this, if the consumer delays the sending of a `VSCMaturedPacket`, we would delay the pruning of the key as well.

### Implementation
The following logic needs to be added to the [HandleConsumerDoubleVoting](https://github.com/cosmos/interchain-security/pull/1232) and [HandleConsumerMisbehaviour](https://github.com/cosmos/interchain-security/pull/826) methods:
```go
undelegationsInTokens := sdk.NewInt(0)
for _, v := range k.stakingKeeper.GetUnbondingDelegationsFromValidator(ctx, validatorAddress) {
    for _, entry := range v.Entries {
        undelegationsInTokens = undelegationsInTokens.Add(entry.InitialBalance)
    }
}

redelegationsInTokens := sdk.NewInt(0)
for _, v := range k.stakingKeeper.GetRedelegationsFromSrcValidator(ctx, validatorAddress) {
    for _, entry := range v.Entries {
        redelegationsInTokens = redelegationsInTokens.Add(entry.InitialBalance)
    }
}

infractionHeight := 0
undelegationsAndRedelegationsInPower = sdk.TokensToConsensusPower(undelegationsInTokens.Add(redelegationsInTokens))
totalPower := validator's voting power + undelegationsAndRedelegationsInPower
slashFraction := k.slashingKeeper.SlashFractionDoubleSign(ctx)

k.stakingKeeper.Slash(ctx, validatorConsAddress, infractionHeight, totalPower, slashFraction, DoubleSign)
```

**Infraction height:** We provide a zero `infractionHeight` to the [Slash](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/staking/keeper/slash.go#L33) method in order to slash all ongoing undelegations and redelegations (see checks in [Slash](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/staking/keeper/slash.go#L92), [SlashUnbondingDelegation](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/staking/keeper/slash.go#L195), and [SlashRedelegation](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0/x/staking/keeper/slash.go#L249)).

**Power:** We pass the sum of the voting power of the misbehaving validator when the evidence was received (i.e., at evidence height) and the power of all the ongoing undelegations and redelegations.
If we assume that the `slashFactor` is `5%`, then the voting power we pass is `power + totalPower(undelegations) + totalPower(redelegations)`.
Hence, when the `Slash` method slashes all the undelegations and redelegations it would end up with `0.05 * power + 0.05 * totalPower(undelegations) + 0.05 * totalPower(redelegations) - 0.05 * totalPower(undelegations) - 0.05 * totalPower(redelegations) = 0.05 * power` and hence it would slash `5%` of the validator's power when the evidence is received.

### Positive
With the proposed approach we can quickly implement slashing functionality on the provider chain for consumer chain equivocations.
This approach does not need to change the staking module and therefore does not change in any way how slashing is performed today for a single chain.

### Negative

- We _definitely_ slash more when it comes to undelegations and redelegations because we slash for all of them without considering an `infractionHeight`.
- We _potentially_ slash more than what we would have slashed if we knew the voting `power` at the corresponding `infractionHeight` in the provider chain.
- We slash on old evidence of equivocation on a consumer.


## References
* [ADR 005: Cryptographic verification of equivocation evidence](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-005-cryptographic-equivocation-verification.md)
* [EPIC tracking cryptographic equivocation feature](https://github.com/cosmos/interchain-security/issues/732)
* [Cosmos Hub Forum discussion on cryptographic equivocation slashing](https://forum.cosmos.network/t/cryptographic-equivocation-slashing-design/11400)
