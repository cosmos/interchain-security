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
In PSS, we introduce a parameter `N` for each consumer chain and require that the validators in top `N%` of the provider's voting power have to secure the consumer chain. 
Additionally, we allow the validators outside of the top `N%` to dynamically opt in if they want to validate on the consumer chain.
For example, if a consumer chain has `N = 95%`, then it ultimately receives the same security it receives today with Replicated Security (with a default [SoftOptOutThreshold](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-009-soft-opt-out.md) of 5%).
On the other hand, if a consumer chain has `N = 0%`, then no validator is forced to validate the chain, but validators can opt in to do so instead.

For the remainder of this ADR, we call a consumer chain _Top N_ if it has joined as a Top N chain with `N > 0` and _Opt In_ chain otherwise.  An Opt In consumer chain is secured only by the validators that have opted in to secure that chain. 

We intend to implement PSS using a feature branch off [v4.0.0 interchain security](https://github.com/cosmos/interchain-security/tree/v4.0.0).

### How do consumer chains join?
As a simplification and to avoid [chain id squatting](https://forum.cosmos.network/t/pss-permissionless-vs-premissioned-lite-opt-in-consumer-chains/12984/17), a consumer chain can only join PSS through a governance proposal and not in a permissionless way.

Consumer chains join PSS the same way chains now join Replicated Security (e.g., see [Stride](https://www.mintscan.io/cosmos/proposals/799)). We extend [`ConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v4.0.0/proto/interchain_security/ccv/provider/v1/provider.proto#L27) with one optional field:

`string top_N_fraction`: Corresponds to the percentage of validators that join under the Top N case.
For example, `0.53` corresponds to a Top 53% chain, meaning that the top `53%` provider validators would validate the proposed consumer chain.
If the `string` is not set, the consumer chain corresponds to an Opt In chain.
`top_N_fraction`  resides between `[0.5, 0.95]`.
Assuming that at most `1/3` of provider validators could be malicious, by having `0.5` (`50%`) as the minimum value for `top_N_fraction` we guarantee that we cannot have a successful invalid-execution attack on a Top N consumer chain. 
This is because, a Top N consumer chain with `N >= 50%` would have at least `1/3` honest validators, which is sufficient to stop any invalid-execution attack.
Additionally, by having `N >= 50%` (and hence `N > 33%`) we enable the top N validators to `Veto` any `ConsumerAdditionProposal` for consumer chains they do not want to validate.

`top_N_fraction` can be up to `0.95` (`95%`) to capture the current case of Replicated Security where we allow the bottom `5%` of validators to opt out. There is no reason for `top_N_fraction` to be higher than `95%`. Smaller chains that belong in the bottom `5%` validators can choose to opt in if they want to validate.


If a proposal has those arguments wrongly set, it should get rejected in [ValidateBasic](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/types/proposal.go#L86).

In the code, we distinguish whether a chain is _Top N_ or _Opt In_ by checking whether `top_N_fraction` is set or not.

In a future version of PSS, we intend to introduce a way to modify the parameters of a consumer chain, e.g, a chain that is _Opt In_ to become _Top N_, etc.

#### State & Query
We augment the provider module’s state to keep track of the `top_N_fraction` value for each consumer chain. The key to store this information would be:

```
topNFractionBytePrefix | len(chainID) | chainID
```
To create the above key, we can use [`ChainIdWithLenKey`](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/types/keys.go#L418).

Then in the [keeper](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/keeper.go) we introduce methods as follows:
```golang
func (k Keeper) SetTopN(ctx sdk.Context, chainID string, topNFraction string)
func (k Keeper) IsTopN(ctx sdk.Context, chainID string) bool
func (k Keeper) IsOptIn(ctx sdk.Context, chainID string) bool

// returns the N if Top N chain, otherwise an error
func (k Keeper) GetTopN(ctx sdk.Context, chainID string) (uint8, error)
```

We also extend the `interchain-security-pd query provider list-consumer-chains` query to return information on whether a consumer chain is an Opt In or a Top N chain and with what N. This way, block explorers like [Mintscan](https://www.mintscan.io/) could show for a chain “This chain is secured by N% of the provider chain.”

### How do validators opt in?
A validator can opt in by sending a new type of message that we introduce in [tx.proto](https://github.com/cosmos/interchain-security/blob/v4.0.0/proto/interchain_security/ccv/provider/v1/tx.proto#L1).
```protobuf
message MsgOptIn {
    // the chain id of the consumer chain to opt in to
    string chain_id = 1;
    // the provider address of the validator
    string provider_addr = 2;
    // (optional) the consensus public key to use on the consumer
    optional string consumer_key = 3;
}
```
Note that in a Top N consumer chain, the top `N%` provider validators have to validate the consumer chain.
Nevertheless, validators in the bottom `(100 - N)%` can opt in to validate as well.
Provider validators that belong to the top `N%` validators are immediately opted in to validate a Top N consumer chain.
This means that if a validator `V` belongs to the top `N%` validators but later falls (e.g., due to undelegations) to the bottom `(100 - N)%`, `V` would still be considered opted in and has to validate unless `V` sends a `MsgOptOut` message (see below).
By automatically opting in validators when they enter the top `N%` of the validators and by forcing top `N%` validators to explicitly opt out in case they fall to the `(100 - N)%` bottom validators we simplify our implementation because i) we only have to find all the opted in validators to retrieve the validators that have to validate a consumer chain, and ii) we simplify reward distribution by preventing cases where we opted out a validator before it receives its rewards.

Note that a validator can send a `MsgOptIn` message even if the consumer chain is not yet running. To do this we reuse the [`IsConsumerProposedOrRegistered`](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/key_assignment.go#L644). If the `chainID` does not exist, the `MsgOptIn` should fail, as well as if the provider address does not exist.

Optionally, a validator that opts in can provide a `consumer_key` so that it assigns a different consumer key (from the provider) to the consumer chain. Naturally, a validator that does not assign a key when opting in can always send a `MsgAssignConsumerKey` to change the consumer key on the consumer chain at a later point in time, as is done in Replicated Security.

#### State & Query
For each validator, we store on whether the validator has  opted in and at the block height they opted in under the key:
```
optedInBytePrefix | len(chainID) | chainID | addr
```
By using a prefix iterator on `optedInBytePrefix | len(chainID) | chainID ` we retrieve all the opted in validators.

We introduce the following `Keeper` methods.
```golang
// returns all the validators that have opted in on chain `chainID`
func (k Keeper) GetOptedInValidators(ctx sdk.Context, chainID string) []Validators

func (k Keeper) IsValidatorOptedIn(ctx sdk.Context, chainID string, val Validator) bool
```

We introduce a query to retrieve the validators that are opted in and hence the validators that need to validate the consumer chain:
```bash
interchain-security-pd query provider optedInValidators $chainID
```

We also introduce a query that given a validator's address returns all the chains this validator has to validate:
```bash
interchain-security-pd query provider hasToValidate providerAddr
```

#### When do validators opt in?
Validators can not only opt in by sending a `MsgOptIn` message, but can also opt in automatically if they voted `Yes`
during the `ConsumerAdditionProposal` that introduced a consumer chain. This simplifies validators operations because
they do not have to send an additional message to opt in.

Because the `Tally` method [deletes the votes](https://github.com/cosmos/cosmos-sdk/blob/v0.47.7/x/gov/keeper/tally.go#L71) after reading them, we cannot check the votes of the validators after the votes have been tallied. To circumvent this, we introduce
a hook for [`AfterProposalVote`](https://github.com/cosmos/cosmos-sdk/blob/v0.47.7/x/gov/keeper/vote.go#L35) and keep track
of all the votes cast by a validator. If a validator votes more than once, we only consider the latest vote.
Finally, we only consider a validator has opted in if it casts a 100% `Yes` vote in case of a [weighted vote](https://github.com/cosmos/cosmos-sdk/blob/main/docs/architecture/adr-037-gov-split-vote.md).


### How do validators opt out?
Validators that have opted in on a chain can opt out as well by sending the following message:

```protobuf
message MsgOptOut {
    // the chain id of the consumer chain to opt out from
    string chain_id = 1;
    // the provider address of the validator
    string provider_addr = 2;
}
```
Validators can only opt out after a consumer chain has started and hence the above message returns an error if the chain with `chain_id` is not running. Additionally, a validator that belongs to the top N% validators cannot opt out from a Top N and hence a `MsgOptOut` would error in such a case.

#### State & Query
We also update the state of the opted-in validators when a validator has opted out by removing it from there.

Note that we only punish validators for downtime that were  opted in in a consumer chain. For this, we keep historical info of all the validators that have opted in during the last `X` (to be defined) blocks. This way we can jail validators for downtime knowing that indeed the validators have opted in at some point in the past. 
Otherwise, we can think of a scenario where a validator `V` is down for a period of time, but before `V` gets punished for downtime, validator `V` opts out and then we do not know whether `V` should be punished or not.

### When does a consumer chain start?
A Top N consumer chain starts at the specified date (`spawn_time`) if the [`ConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v4.0.0/proto/interchain_security/ccv/provider/v1/provider.proto#L27) has passed. An Opt In consumer chain starts if at least one validator has opted in. We check this in [BeginBlockInit](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/proposal.go#L357):
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
To send the validator set to a consumer chain we first have to generate the validator updates with a function similar to this one:

```golang
func (k Keeper) GetPartialSetValidators(ctx types.Context, chainID string, valUpdates []abci.ValidatorUpdate) (newUpdates []abci.ValidatorUpdate)

    powerSum := sdk.ZeroDec()
    totalPower := k.ComputeTotalPower(ctx)
    topNThreshold := k.GetTopN(ctx, chainID) / 100
    for _, val := range valUpdates {
        powerSum = powerSum.Add(sdk.NewDecFromInt(sdk.NewInt(val.Power)))
        // if powerSum / totalPower > topNThreshold
        if k.IsTopN(ctx, chainID) && powerSum.Quo(totalPower).GT(topNThreshold) {
            // is Top N validator
            updates = append(updates, abci.ValidatorUpdate{
                PubKey: val.PubKey,
                Power:  val.Power,
            })
       } else {
       if k.IsValidatorOptedIn(ctx, chainID, val.PubKey) {
            updates = append(updates, abci.ValidatorUpdate{
                PubKey: val.PubKey,
                Power:  val.Power,
            })
        } else {
            // remove this validator
            updates = append(updates, abci.ValidatorUpdate{
                PubKey: val.PubKey,
                Power:  0,
            })
        }
    }

    return updates
}
```
And then we change `QueueVSCPackets` to:

```golang
// QueueVSCPackets queues latest validator updates for every registered consumer chain
func (k Keeper) QueueVSCPackets(ctx sdk.Context) {
    valUpdateID := k.GetValidatorSetUpdateId(ctx) // current valset update ID
    // Get the validator updates from the staking module.
    // Note: GetValidatorUpdates panics if the updates provided by the x/staking module
    // of cosmos-sdk is invalid.
    valUpdates := k.stakingKeeper.GetValidatorUpdates(ctx)

    for _, chain := range k.GetAllConsumerChains(ctx) {
        // Apply the key assignment to the validator updates.
        valUpdates := k.GetPartialSetValidators(ctx, chain.ChainId, valUpdates)
        valUpdates := k.MustApplyKeyAssignmentToValUpdates(ctx, chain.ChainId, valUpdates)
        ...
```

Note that we use `0` to remove validators that are not opted in as described [here](https://docs.cometbft.com/v0.37/spec/abci/abci++_methods#endblock) and as is done for the [assignment of consumer keys](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/key_assignment.go#L525).

### How do we distribute rewards?
Currently, rewards are distributed as follows: The consumer [periodically sends rewards](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/consumer/keeper/distribution.go#L148) on the provider `ConsumerRewardsPool` address.
The provider then [transfers those rewards to the fee collector address](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/distribution.go#L77) and those transferred rewards are distributed to validators and delegators.

In PSS, we distribute rewards only to validators that actually validate the consumer chain. To do this, we have a pool associated with each consumer chain and consumers IBC transfer the rewards to this pool.
Then, because we do not use the canonical fee pool and hence rewards are not automatically distributed, we will create a new and modified version of [AllocateTokens](https://github.com/cosmos/cosmos-sdk/blob/v0.47.7/x/distribution/keeper/allocation.go#L14) as follows:

```golang
func (k Keeper) AllocateTokensFromPool(ctx sdk.Context, poolAddress string, totalPreviousPower int64, bondedVotes []abci.VoteInfo) {
	rewardsCollectedInt := k.bankKeeper.GetAllBalances(ctx, poolAddress)
	// rest in the same that `AllocateTokens` operates
	...
```

In [TransferRewardsToFeeCollector](https://github.com/cosmos/interchain-security/blob/v4.0.0/x/ccv/provider/keeper/distribution.go#L61) we then do:

```golang
for _, chain := range consumerChains {
    ...
    totalPower := 0
    var []abci.VoteInfo votes
    for _, val := range (validators that opted in or Top N) {
        if val has opted in for more than X blocks {
            votes = append(votes, []abci.VoteInfo{{Validator: val, SignedLastBlock: true}})
        }
    }
    
    k.AllocateTokens(ctx, pool associated with this chain, totalPower, votes)
    ...
}
```

instead of calling:
```golang
// 4. Transfer the balance to the fee collector address
err := k.bankKeeper.SendCoinsFromModuleToModule(
    ctx,
    types.ConsumerRewardsPool,
    k.feeCollectorName,
    sdk.NewCoins(balance),
)
```

Note that we would only distribute rewards to validators that are opted in but are opted in for some time (e.g., 10000 blocks) to avoid cases where validators opt in and out in short intervals just in order to receive rewards.

### Misbehaviour

#### Fraud votes
In an Opt In chain, a set of validators might attempt to perform an invalid-execution attack. To deter such potential attacks, PSS allows for the use of fraud votes.
A _fraud vote_ is a governance proposal that enables the slashing of validators that performed an invalid-execution attack.
Due to their inherent complexity, we intend to introduce fraud votes in a different ADR and at a future iteration of PSS. 


#### Double signing
We do not change the way slashing for double signing and light client attacks functions. If a validator misbehaves on a consumer, then we slash that validator on the provider.

#### Downtime
We do not change the way downtime jailing functions. If a validator is down on a consumer chain for an adequate amount of time, we jail this validator on the provider only if the validator was opted in in the recent past.

## Consequences

### Positive
- Easier for new consumer chains to consume the provider's chain security because proposals are more likely to pass if not everyone is forced to validate.
- Small validators are not forced to validate chains anymore if they do not want to.

### Negative
- Depending on whether a consumer chain is Top N or Opt In, a consumer chain might not be as secure as with Replicated Security.


## References

- [PSS: Permissionless vs premissioned-lite opt-in consumer chains](https://forum.cosmos.network/t/pss-permissionless-vs-premissioned-lite-opt-in-consumer-chains/12984)
- [CHIPs discussion phase: Partial Set Security (updated)](https://forum.cosmos.network/t/chips-discussion-phase-partial-set-security-updated/11775)
- [PSS: Exclusive vs Inclusive Top-N](https://forum.cosmos.network/t/pss-exclusive-vs-inclusive-top-n/13058)
- [Initial PSS ADR and notes #1518](https://github.com/cosmos/interchain-security/pull/1518)
- [Replicated vs. Mesh Security](https://informal.systems/blog/replicated-vs-mesh-security) 
