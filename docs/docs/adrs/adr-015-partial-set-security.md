---
sidebar_position: 16
title: Partial Set Security
---
# ADR 015: Partial Set Security

## Changelog

* 2024-01-22: Proposed, first draft of ADR.

## Status

Proposed

## Context

Currently, in _Replicated Security_, the entire validator set of the provider chain is used to secure consumer chains. There are at least three concerns with this approach.
First, a large number of validators might be forced to validate consumer chains they are not interested in securing.
Second, it is costly for small validators to secure additional chains. This concern is only partially addressed through [soft opt-out](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-009-soft-opt-out.md) that allows small validators to opt out from validating consumer chains.
Third and for the above reasons, it is challenging for a new consumer chain to join Replicated Security.

As a solution, we present _Partial Set Security_ (PSS). As the name suggests, PSS allows for every consumer chain to be secured by only a subset of the provider validator set.
In what follows we propose the exact steps we need to take to implement PSS. This is a first iteration of PSS, and therefore we present the most minimal solution that make PSS possible.

## Decision

In Replicated Security, all the provider validators have to secure every consumer chain (with the exception of those validators allowed to opt out through the [soft opt-out](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-009-soft-opt-out.md) feature).

In PSS, we allow validators to opt in and out of validating any given consumer chain.
This has one exception:  we introduce a parameter `N` for each consumer chain and require that the validators in top `N%` of the provider's voting power have to secure the consumer chain.
Validators outside of the top `N%` can dynamically opt in if they want to validate on the consumer chain.

For example, if a consumer chain has `N = 95%`, then it ultimately receives the same security it receives today with Replicated Security (with a default [SoftOptOutThreshold](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-009-soft-opt-out.md) of 5%).
On the other hand, if a consumer chain has `N = 0%`, then no validator is forced to validate the chain, but validators can opt in to do so instead.

For the remainder of this ADR, we call a consumer chain _Top N_ if it has joined as a Top N chain with `N > 0` and _Opt In_ chain otherwise.  An Opt In consumer chain is secured only by the validators that have opted in to secure that chain.

We intend to implement PSS using a feature branch off [v4.0.0 interchain security](https://github.com/cosmos/interchain-security/tree/v4.0.0).

### How do consumer chains join?

As a simplification and to avoid [chain id squatting](https://forum.cosmos.network/t/pss-permissionless-vs-premissioned-lite-opt-in-consumer-chains/12984/17), a consumer chain can only join PSS through a governance proposal and not in a permissionless way.

However, this proposal type will be modified so that it requires a lower quorum percentage than normal proposal, and every validator who voted "YES" on the proposal will form the consumer chain's initial validator set.

Consumer chains join PSS the same way chains now join Replicated Security, namely through a `ConsumerAdditionProposal` proposal.
We extend [`ConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v4.0.0/proto/interchain_security/ccv/provider/v1/provider.proto#L27) with one optional field:

`uint32 top_N`: Corresponds to the percentage of validators that join under the Top N case.
For example, `53` corresponds to a Top 53% chain, meaning that the top `53%` provider validators have to validate the proposed consumer chain.
`top_N`  can be `0` or include any value in `[50, 100]`. A chain can join with `top_N == 0` as an Opt In, or with `top_N ∈ [50, 100]` as a Top N chain.

In case of a Top N chain, we restrict the possible values of `top_N` from `(0, 100]` to `[50, 100]`.
By having `top_N >= 50` we can guarantee that we cannot have a successful attack, assuming that at most `1/3` of provider validators can be malicious.
This is because, a Top N chain with `N >= 50%` would have at least `1/3` honest validators, which is sufficient to stop attacks.
Additionally, by having `N >= 50%` (and hence `N > (VetoThreshold = 33.4%)`) we enable the top N validators to `Veto` any `ConsumerAdditionProposal` for consumer chains they do not want to validate.

If a proposal has the `top_N` argument wrongly set, it should get rejected in [ValidateBasic] (<https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/types/proposal.go#L86>).

In the code, we distinguish whether a chain is _Top N_ or _Opt In_ by checking whether `top_N` is zero or not.

In a future version of PSS, we intend to introduce a `ConsumerModificationProposal` so that we can modify the parameters of a consumer chain, e.g, a chain that is _Opt In_ to become _Top N_, etc.

#### State & Query

We augment the provider module’s state to keep track of the `top_N` value for each consumer chain. The key to store this information would be:

```
topNBytePrefix | len(chainID) | chainID
```

To create the above key, we can use [`ChainIdWithLenKey`](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/types/keys.go#L418).

Then in the [keeper](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/keeper.go) we introduce methods as follows:

```golang
func (k Keeper) SetTopN(ctx sdk.Context, chainID string, topN uint32)
func (k Keeper) IsTopN(ctx sdk.Context, chainID string) bool
func (k Keeper) IsOptIn(ctx sdk.Context, chainID string) bool

// returns the N if Top N chain, otherwise an error
func (k Keeper) GetTopN(ctx sdk.Context, chainID string) (uint32, error)
```

We also extend the `interchain-security-pd query provider list-consumer-chains` query to return information on whether a consumer chain is an Opt In or a Top N chain and with what N.
This way, block explorers can present informative messages such as "This chain is secured by N% of the provider chain" for consumer chains.

### How do validators opt in?

A validator can opt in by sending a new type of message that we introduce in [tx.proto](https://github.com/cosmos/interchain-security/blob/v4.0.0/proto/interchain_security/ccv/provider/v1/tx.proto#L1).

```protobuf
message MsgOptIn {
    // the chain id of the consumer chain to opt in to
    string chainID = 1;
    // the provider address of the validator
    string providerAddr = 2;
    // (optional) the consensus public key to use on the consumer
    optional string consumerKey = 3;
}
```

Note that in a Top N consumer chain, the top `N%` provider validators have to validate the consumer chain.
Nevertheless, validators in the bottom `(100 - N)%` can opt in to validate as well.
Provider validators that belong or enter the top `N%` validators are _automatically_ opted in to validate a Top N consumer chain.
This means that if a validator `V` belongs to the top `N%` validators but later falls (e.g., due to undelegations) to the bottom `(100 - N)%`, `V` is still considered opted in and has to validate unless `V` sends a `MsgOptOut` message (see below).
By automatically opting in validators when they enter the top `N%` validators and by forcing top `N%` validators to explicitly opt out in case they fall to the `(100 - N)%` bottom validators we simplify the design of PSS.

Note that a validator can send a `MsgOptIn` message even if the consumer chain is not yet running. To do this we reuse the [`IsConsumerProposedOrRegistered`](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/key_assignment.go#L644). If the `chainID` does not exist, the `MsgOptIn` should fail, as well as if the provider address does not exist.

Optionally, a validator that opts in can provide a `consumerKey` so that it assigns a different consumer key (from the provider) to the consumer chain.
Naturally, a validator can always change the consumer key on a consumer chain by sending a `MsgAssignConsumerKey` message at a later point in time, as is done in Replicated Security.

#### State & Query

For each validator, we store a pair `(blockHeight, isOptedIn)` that contains the block height the validator opted in and whether the validator is currently opted in or not, under the key:

```
optedInBytePrefix | len(chainID) | chainID | addr
```

By using a prefix iterator on `optedInBytePrefix | len(chainID) | chainID` we retrieve all the opted in validators.

We introduce the following `Keeper` methods.

```golang
// returns all the validators that have opted in on chain `chainID`
func (k Keeper) GetOptedInValidators(ctx sdk.Context, chainID string) []Validators

func (k Keeper) IsValidatorOptedIn(ctx sdk.Context, chainID string, val Validator) bool
```

We introduce the following two queries:

```bash
interchain-security-pd query provider optedInValidators $chainID
interchain-security-pd query provider hasToValidate $providerAddr
```

One query to retrieve the validators that are opted in and hence the validators that need to validate the consumer chain and one query that given a validator's address returns all the chains this validator has to validate.

#### When do validators opt in?

As described earlier, validators can manually opt in by sending a `MsgOptIn` message.
Additionally, in a Top N chain, a validator is automatically opted in when it moves from the bottom `(100 - N)%` to the top `N%` validators.

Lastly, validators can also opt in if they vote `Yes` during the `ConsumerAdditionProposal` that introduces a consumer chain.
This simplifies validators operations because they do not have to send an additional message to opt in.

Because the `Tally` method [deletes the votes](https://github.com/cosmos/cosmos-sdk/blob/v0.47.7/x/gov/keeper/tally.go#L71) after reading them, we cannot check the votes of the validators after the votes have been tallied.
To circumvent this, we introduce a hook for [`AfterProposalVote`](https://github.com/cosmos/cosmos-sdk/blob/v0.47.7/x/gov/keeper/vote.go#L35) and keep track of all the votes cast by a validator.
If a validator casts more than one vote, we only consider the latest vote.
Finally, we only consider a validator has opted in if it casts a 100% `Yes` vote in case of a [weighted vote](https://github.com/cosmos/cosmos-sdk/blob/main/docs/architecture/adr-037-gov-split-vote.md).

### How do validators opt out?

Validators that have opted in on a chain can opt out by sending the following message:

```protobuf
message MsgOptOut {
    // the chain id of the consumer chain to opt out from
    string chainID = 1;
    // the provider address of the validator
    string providerAddr = 2;
}
```

Validators can only opt out after a consumer chain has started and hence the above message returns an error if the chain with `chainID` is not running.
Additionally, a validator that belongs to the top `N%` validators cannot opt out from a Top N chain and hence a `MsgOptOut` would error in such a case.

#### State & Query

We also update the state of the opted-in validators when a validator has opted out by removing the opted-out validator.

Note that only opted-in validators can be punished for downtime on a consumer chain.
For this, we use historical info of all the validators that have opted in; We can examine the `blockHeight` stored under the key `optedInBytePrefix | len(chainID) | chainID | addr` to see if a validator was opted in.
This way we can jail validators for downtime knowing that indeed the validators have opted in at some point in the past.
Otherwise, we can think of a scenario where a validator `V` is down for a period of time, but before `V` gets punished for downtime, validator `V` opts out, and then we do not know whether `V` should be punished or not.

### When does a consumer chain start?

A Top N consumer chain always starts at the specified date (`spawn_time`) if the [`ConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v4.0.0/proto/interchain_security/ccv/provider/v1/provider.proto#L27) has passed.
An Opt In consumer chain only starts if at least one validator has opted in. We check this in [BeginBlockInit](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/proposal.go#L357):

```golang
func (k Keeper) BeginBlockInit(ctx sdk.Context) {
    propsToExecute := k.GetConsumerAdditionPropsToExecute(ctx)

    for _, prop := range propsToExecute {
        chainID := prop.ChainId
        if !k.IsTopN(ctx, chainID) && len(k.GetOptedInValidators(ctx, chainID)) == 0 {
            // drop the proposal
            ctx.Logger().Info("could not start chain because no validator has opted in")
            continue
        }   
        ...
```

### How do we send the partial validator sets to the consumer chains?

A consumer chain should only be validated by opted in validators.
We introduce logic to do this when we [queue](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/relay.go#L213) the `VSCPacket`s.
The logic behind this, is not as straightforward as it seems because CometBFT does not receive the validator set that has to validate a chain, but rather a delta of [validator updates](https://docs.cometbft.com/v0.37/spec/abci/abci++_methods#validatorupdate).
For example, to remove an opted-out validator from a consumer chain, we have to send a validator update with a `power` of `0`, similarly to what is done in the [assignment of consumer keys](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/key_assignment.go#L525).
We intend to update this ADR at a later stage on how exactly we intend to implement this logic.

### How do we distribute rewards?

Currently, rewards are distributed as follows: The consumer [periodically sends rewards](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/consumer/keeper/distribution.go#L148) on the provider `ConsumerRewardsPool` address.
The provider then [transfers those rewards to the fee collector address](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/distribution.go#L77) and those transferred rewards are distributed to validators and delegators.

In PSS, we distribute rewards only to validators that actually validate the consumer chain.
To do this, we have a pool associated with each consumer chain and consumers IBC transfer the rewards to this pool.
We then extract the rewards from each consumer pool and distribute them to the opted in validators.

Note that we only distribute rewards to validators that have been opted in for some time (e.g., 10000 blocks) to avoid cases where validators opt in just to receive rewards and then opt out immediately afterward.

### Misbehaviour

#### Fraud votes

In an Opt In chain, a set of validators might attempt to perform an attack. To deter such potential attacks, PSS allows for the use of fraud votes.
A _fraud vote_ is a governance proposal that enables the slashing of validators that performed an attack.
Due to their inherent complexity, we intend to introduce fraud votes in a different ADR and at a future iteration of PSS.

#### Double signing

We do not change the way slashing for double signing and light client attacks functions.
If a validator misbehaves on a consumer, then we slash that validator on the provider.

#### Downtime

We do not change the way downtime jailing functions.
If a validator is down on a consumer chain for an adequate amount of time, we jail this validator on the provider but only if the validator was opted in on this consumer chain in the recent past.

## Consequences

### Positive

* Easier for new consumer chains to consume the provider's chain economic security because proposals are more likely to pass if not everyone is forced to validate.

* Smaller validators are not forced to validate chains anymore if they do not want to.
* We can deprecate the soft opt-out implementation.

### Negative

* A consumer chain does not receive the same economic security as with Replicated Security (assuming the value of `SoftOptOutThreshold` is `5%`), unless it is a Top N chain with `N >= 95%`.

## References

* [PSS: Permissionless vs premissioned-lite opt-in consumer chains](https://forum.cosmos.network/t/pss-permissionless-vs-premissioned-lite-opt-in-consumer-chains/12984)
* [CHIPs discussion phase: Partial Set Security (updated)](https://forum.cosmos.network/t/chips-discussion-phase-partial-set-security-updated/11775)
* [PSS: Exclusive vs Inclusive Top-N](https://forum.cosmos.network/t/pss-exclusive-vs-inclusive-top-n/13058)
* [Initial PSS ADR and notes #1518](https://github.com/cosmos/interchain-security/pull/1518)
* [Replicated vs. Mesh Security](https://informal.systems/blog/replicated-vs-mesh-security)
