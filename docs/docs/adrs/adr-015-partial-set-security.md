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
Currently, in _Replicated Security_, the **whole** validator set of the Cosmos Hub _provider chain_ is used to secure consumer chains. There are at least three concerns with this approach. First, a big chunk of validators might be forced to validate consumer chains they are not interested in securing. Second, it is costly for small validators to secure additional chains. This concern is only partially addressed through [soft opt-out](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-009-soft-opt-out.md) where the bottom (based on voting power) 5% validator can opt out from validating consumer chains. Third and for the above reasons, it is challenging for a new consumer chain to join Replicated Security.

As a solution, we present _Partial Set Security_ (PSS). As the name suggests, PSS allows for every consumer chain to be secured by only a subset of the provider validator set. 
In what follows we propose the exact steps we need to take to implement PSS. This is a first iteration of Partial Set Security, and therefore we present the most minimal solution that make PSS possible.

## Decision
In Replicated Security, all the provider validators have to secure every consumer chain (with the exception of those validators allowed to opt out through the [soft opt-out](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-009-soft-opt-out.md) feature). 
In Partial Set Security (PSS), we introduce a parameter `N` for each consumer chain and require that the validators in top `N%` of the provider's voting power have to secure the consumer chain. 
Additionally, we allow the validators outside of the top `N%` to dynamically opt in if they want to validate on the consumer chain.
For example, if a consumer chain has `N = 95%`, then it ultimately receives the same security it receives today by Replicated Security. On the other hand, if a consumer chain has `N = 0`%, then no validator is forced to validate the chain but validators can opt in to do so instead.
In what follows, we call a consumer chain _Top N_ if it has joined as Top N chain with `N > 0` and _Opt In_ chain otherwise.  An Opt In consumer chain is secured only by the validators that have opted in to secure that chain.

We intend to implement PSS using a feature branch off [v3.3.0 interchain security](https://github.com/cosmos/interchain-security/tree/v3.3.0).

### How do consumer chains join?
As a [simplification](https://forum.cosmos.network/t/pss-permissionless-vs-premissioned-lite-opt-in-consumer-chains/12984/17), a consumer chain can only join Partial Set Security through a governance proposal and not in a permissionless way.

Consumer chains join Partial Set Security the same way chains now join Replicated Security (e.g., see [Stride](https://www.mintscan.io/cosmos/proposals/799)). We extend [`ConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v3.3.0/proto/interchain_security/ccv/provider/v1/provider.proto#L27) with 2 optional fields:
`bool is_top_N`: flag that captures whether the consumer chain joins under the Top N case.
`int8 top_N`: value that captures the percentage of the Top N% validators that should validate this consumer chain. This is only set if `is_top_N` is `true`.

Note that `top_N` resides between `[50, 95]`.
Assuming that at most `1/3` of validators could be malicious, by having 50% as the minimum value for `top_N` we guarantee that we cannot have a successful incorrect-execution attack on a Top N consumer chain. This is because, a Top N consumer chain with `N >= 50%` would have at least `1/3` correct validators that would be able to censor any incorrect-execution attack.
Additionally, by having a `N >= 50%` and hence `N > 33%` we provide the ability for validators to `Veto` a `ConsumerAdditionProposal` if they do not desire to validate a consumer chain.

`top_N` can be up to 95% to capture the current case of Replicated Security where we allow the bottom 5% of validators to opt out. There is no reason for `top_N` to be higher than 95%. Smaller chains that belong in the bottom 5% validators can choose to opt in if they want to validate.

So, the fields can take the following values:
| `is_top_N` | `top_N`|
| :--- | :---|
| `true` | `[50, 95]` |
| `false` | not set |


If a proposal has those arguments wrongly set, it should get rejected in [ValidateBasic](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/types/proposal.go#L86).

Note that we could easily distinguish whether a chain is _Top N_ or _Opt In_ by only having the single field `top_N` and if `top_N == 0`, then we’re in the _Opt In_ case, although for clarity, we introduce both fields.

In a future version of PSS, we intend to introduce a way to modify the parameters of a consumer chain, e.g, a chain that is _Opt In_ to become _Top N_, etc.

#### State & Query
We augment the provider module’s state to keep track of the `is_top_N` and `top_N` values for each consumer chain. The key to store this information would be:

```
ChainIdWithLenKey(IsTopNBytePrefix, chainID)
```
reusing [`ChainIdWithLenKey`](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/types/keys.go#L418).

Then in the [keeper](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/keeper/keeper.go) we introduce methods as follows:
```
func (k Keeper) SetIsTopN(ctx sdk.Context, chainID string, isTopN bool) error
func (k Keeper) IsTopN(ctx sdk.Context, chainID string) bool

// returns the N if Top N chain, otherwise an error
func (k Keeper) GetTopN(ctx sdk.Context, chainID string) (uint8, error)
```

In a future version of PSS, we intend to extend the `interchain-security-pd query provider list-consumer-chains` query to also return information on whether a consumer chain is an Opt In or a Top N chain and with what N. This way, block explorers like [Mintscan](https://www.mintscan.io/) would show for a chain “This chain is secured by N% of Cosmos Hub.”

### How do validators opt in?
A validator can opt in by sending a new type of message that we introduce in [tx.proto](https://github.com/cosmos/interchain-security/blob/v3.3.0/proto/interchain_security/ccv/provider/v1/tx.proto#L1).
```
message MsgOptIn {
    // the chain id of the consumer chain to opt in to
    string chain_id = 1;
    // the provider address of the validator on Cosmos Hub
    string provider_addr = 2;
}
```
Note that in a Top N consumer chain, the top N% Cosmos Hub validators are forced by default to validate the consumer chain. Nevertheless, validators in the bottom 100 - N% can opt in to validate as well.
Additionally, note that due to undelegations, etc. a validator that is in the top N% validators might fall down to the 100 - N% in which case this validator is not forced to validate anymore. Therefore, a validator that might move out of the top N% might want to send a `MsgOptIn` to keep validating even if this happens.

Note that a validator can send a `MsgOptIn` message even if the consumer chain is not yet running. To do this we reuse the [`IsConsumerProposedOrRegistered`](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/keeper/key_assignment.go#L644). If the `chainID` does not exist, the `MsgOptIn` should fail, as well as if the provider address does not exist.

Additionally, a validator that opts in can then use `MsgAssignConsumerKey` to change the consumer key on the consumer chain as is currently done in Replicated Security.

#### State & Query
We store the list of validators that have opted in and at the block height they opted it in under the key:
```
ChainIdWithLenKey(OptedInByteKey, chainID)
```

And for simplicity for each validator we store a boolean on whether this validator has opted in on this chain or not.
```
ChainIdAndConsAddrKey(OptedInByteKey, chainID, addr)
```

We augment the state of the provider to keep track for each chain all the validators that have opted in and if a specific validator has opted in.
```
// returns all the validators that have opted in on chain `chainID`
func (k Keeper) GetOptedInValidators(ctx sdk.Context, chainID string) []Validators

func (k Keeper) IsValidatorOptedIn(ctx sdk.Context, chainID string, val Validator) bool
```

We introduce a query to retrieve the validators that are opted in. The query would operate as follows.
```
gaiad query provider optedInValidators $chainId
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

```
message MsgOptOut {
    // the chain id of the consumer chain to opt out from
    string chain_id = 1;
    // the provider address of the validator on Cosmos Hub
    string provider_addr = 2;
}
```
Validators can only opt out after a consumer chain has started and hence the above message returns an error if the chain with `chain_id` is not running.

#### State & Query
We also update the state of the opted-in validators when a validator has opted out by removing it from there.
Nevertheless, we have to keep track of all the validators that have opted in during the last `X` (to be defined) blocks to be able to jail validators for downtime.

### When does a consumer chain start?
A Top N consumer chain starts at the specified date (`spawn_time`) if the [`ConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v3.3.0/proto/interchain_security/ccv/provider/v1/provider.proto#L27) has passed. An Opt In consumer chain starts if at least one validator has opted in. We check this in [BeginBlockInit](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/keeper/proposal.go#L372):
```
func (k Keeper) BeginBlockInit(ctx sdk.Context) {
    propsToExecute := k.GetConsumerAdditionPropsToExecute(ctx)

    for _, prop := range propsToExecute {
        chainId := prop.ChainId
        if !k.IsTopN(ctx, chainId) && len(k.GetOptedInValidators(ctx, chainId)) == 0 {
            // drop the proposal
            ctx.Logger().Info("could not start chain because noone has opted in")
            continue
        }   
        ...
```

### How do we send the partial validator sets to the consumer chains?
To send the validator set to a consumer chain we first have to generate the validator updates with a function similar to this one:

```
func (k Keeper) GetPartialSetValidators(ctx types.Context, chainId string, valUpdates []abci.ValidatorUpdate) (newUpdates []abci.ValidatorUpdate)

    powerSum := sdk.ZeroDec()
    totalPower := k.ComputeTotalPower(ctx)
    topNThreshold := k.GetTopN(ctx, chainId) / 100
    for _, val := range valUpdates {
        powerSum = powerSum.Add(sdk.NewDecFromInt(sdk.NewInt(val.Power)))
        // if powerSum / totalPower > topNThreshold
        if k.IsTopN(ctx, chainId) && powerSum.Quo(totalPower).GT(topNThreshold) {
            // is Top N validator
            updates = append(updates, abci.ValidatorUpdate{
                PubKey: val.PubKey,
                Power:  val.Power,
            })
       } else {
       if k.IsValidatorOptedIn(ctx, chainId, val.PubKey) {
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

```
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

Note that we use `0` to remove validators that are not opted in as described [here](https://docs.cometbft.com/v0.37/spec/abci/abci++_methods#endblock) and as is done for the [assignment of consumer keys](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/keeper/key_assignment.go#L525).

### How do we distribute rewards?
Currently, rewards are distributed as follows: The consumer [periodically sends rewards](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/consumer/keeper/distribution.go#L148) on the provider `ConsumerRewardsPool` address.
The provider then [transfers those rewards to the fee collector address](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/keeper/distribution.go#L77) and those transferred rewards are distributed to validators and delegators.

In PSS, we distribute rewards only to validators that actually validate the consumer chain. To do this, we have a pool associated with each consumer chain and consumers IBC transfer the rewards to this pool.
Then, because we do not use the canonical fee pool and hence rewards are not automatically distributed, we will create a new and modified version of [AllocateTokens](https://github.com/cosmos/cosmos-sdk/blob/v0.47.7/x/distribution/keeper/allocation.go#L14) as follows:

```
func (k Keeper) AllocateTokensFromPool(ctx sdk.Context, poolAddress string, totalPreviousPower int64, bondedVotes []abci.VoteInfo) {
	rewardsCollectedInt := k.bankKeeper.GetAllBalances(ctx, poolAddress)
	// rest in the same that `AllocateTokens` operates
	...
```

In [TransferRewardsToFeeCollector](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/keeper/distribution.go#L61) we then do:

```
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
```
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
For fraud votes, we add a new type `FraudVoteProposal` similar to [EquivocationProposal](https://github.com/cosmos/interchain-security/pull/703). The time to detect incorrect execution evidence is 7 days (the same time as that of detecting a light client attack on a client with a `trustingPeriod` of 14 days); We have 7 days to detect an incorrect execution and then 14 days for the proposal to be accepted.

##### When are fraud votes eligible?
Because fraud votes allow the slashing of a validator through a governance proposal, we are cautious on when a fraud vote is eligible and try to restrict their eligibility as much as possible to avoid an adversary proposing a bogus fraud vote.
As described earlier, because in Top N chains we consider that `N > 50%` we only consider validators that have opted in an Opt In chain. Fraud votes are also **only** intended to be used for **malicious** behaviour, for example, in a scenario similar to what [happened to Neutron](https://blog.neutron.org/neutron-halt-post-mortem-927dbe4540c8), validators should vote against slashing those validators.

#### Message
```
message FraudVoteProposal {
    string title = 1;
    string description = 2;
    
    // validator that performed incorrect execution (consensus address on consumer chain)
    Validator validator = 3;
    
    // validator's vote contains BlockId on what was signed
    Vote vote = 4;
    
    // header for which the hash led to the blockId in the vote
    Header header = 5;
}
```

The message includes the `vote` that was signed by the validator. Validators that vote on a fraud vote can look at the `BlockID` contained in a `vote` and the `appHash`, `lastResultHash`, etc. in the `header` (that led to this `BlockID`) to conclude whether the to-be-voted validator has performed incorrect execution or not.

#### Double signing
We do not change the way slashing for double signing and light client attacks functions. If a validator misbehaves on a consumer, then we slash that validator on the provider.

#### Downtime
We do not change the way downtime jailing functions. If a validator is down on a consumer chain for an adequate amount of time, we jail this validator on Cosmos Hub only if the validator was opted in in the recent past.

## Consequences

### Positive
- Easier for new consumer chains to consume Cosmos Hub security because proposals are more likely to pass if not everyone is forced to validate.
- Small validators are not forced to validate chains anymore if they do not want to.

### Negative
- Fraud votes introduce one more way to slash validators.
- Depending on whether a consumer chain is Top N or Opt In, a consumer chain might not be as secure as with Replicated Security.


## References

- [PSS: Permissionless vs premissioned-lite opt-in consumer chains](https://forum.cosmos.network/t/pss-permissionless-vs-premissioned-lite-opt-in-consumer-chains/12984)
- [CHIPs discussion phase: Partial Set Security (updated)](https://forum.cosmos.network/t/chips-discussion-phase-partial-set-security-updated/11775)
- [PSS: Exclusive vs Inclusive Top-N](https://forum.cosmos.network/t/pss-exclusive-vs-inclusive-top-n/13058)
- [Initial PSS ADR and notes #1518](https://github.com/cosmos/interchain-security/pull/1518)
- [Replicated vs. Mesh Security](https://informal.systems/blog/replicated-vs-mesh-security) 
