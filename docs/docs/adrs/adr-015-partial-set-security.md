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

As a solution, we present _Partial Set Security_ (PSS). As the name suggests, PSS allows for only a subset of the validator set of Cosmos to secure a consumer chain. In what follows we propose the exact steps we need to take to implement PSS. This is a first iteration of Partial Set Security, and therefore we present the most minimal solution that achieves PSS possible.

## Decision
In Replicated Security, 95% (see  soft opt-out) of the top Cosmos Hub validators have to secure a consumer chain. In Partial Set Security (PSS) we introduce a parameter `N` that is associated with a consumer chain and require that the top `N%` of the Cosmos Hub validators have to secure this consumer chain. Additionally, we allow validators that do not belong to the top `N%` of the Cosmos Hub validators to dynamically opt in if they want to validate on the consumer chain or not.
For example, if a consumer chain has `N = 95%`, then it ultimately receives the same security it receives today by Replicated Security. On the other hand, if a consumer chain has `N = 0`%, then no validator is forced to validate the chain but validators can opt in to do so instead.
In what follows, we call a consumer chain _Top N_ if it has joined as Top N chain with `N > 0` and _Opt In_ chain otherwise.  An Opt In consumer chain is secured only by the validators that have opted in to secure that chain.

We intend to implement PSS using a feature branch off [v3.3.0 interchain security](https://github.com/cosmos/interchain-security/tree/v3.3.0).

### How do consumer chains join?
As a [simplification](https://forum.cosmos.network/t/pss-permissionless-vs-premissioned-lite-opt-in-consumer-chains/12984/17), a consumer chain can only join Partial Set Security through a governance proposal and not in a permissionless way.

Consumer chains join Partial Set Security the same way chains now join Replicated Security (e.g., see [Stride](https://www.mintscan.io/cosmos/proposals/799)). We extend [`ConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v3.3.0/proto/interchain_security/ccv/provider/v1/provider.proto#L27) with 2 optional fields:
`bool is_top_N`: flag that captures whether the consumer chain joins under the Top N case.
`int8 top_N`: value that captures the percentage of the Top N% validators that should validate this consumer chain. This is only set if `is_top_N` is `true`.

Note that `top_N` can be between `[34, 95]`. `top_N` cannot be less than 34 (~⅓) because in the case of `Top N` we want to give the ability to the top 33% validators to veto a proposal so that they are not forced by the remaining validators to secure a consumer chain they do not want to secure. `top_N` can be up to 95% to capture the current case Replicated Security where we allow the bottom 5% of validators to opt out. There is no reason for `top_N` to be higher than 95%. Smaller chains that belong in the bottom 5% validators can choose to opt in if they want to validate.

So, the fields can take the following values:
| `is_top_N` | `top_N`|
| :--- | :---|
| `true` | `[34, 95]` |
| `false` | not set |


If a proposal has those arguments wrongly set, it should get rejected in [ValidateBasic](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/types/proposal.go#L86).

Note that we could easily distinguish whether a chain is _Top N_ or _Opt In_ by only having the single field `top_N` and if `top_N == 0`, then we’re in the _Opt In_ case, although for clarity, we introduce both fields.

In a future version of PSS, we intend to introduce a way to modify the parameters of a consumer chain, e.g, a chain that is _Opt In_ to become _Top N—, etc.

#### State & Query
We have to augment the provider module’s state to keep track of the `is_top_N` and `top_N` values for each consumer chain. They key to store this information would be:

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

In a future version of PSS, we intend to extend the `gaiad query provider list-consumer-chains` query to also return information on whether a consumer chain is an Opt In or a Top N chain and with what N. This way, block explorers like [Mintscan](https://www.mintscan.io/) would show for a chain “This chain is secured by N% of Cosmos Hub.”

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
We store the list of validators that have opted in under the key:
```
ChainIdAndConsAddrKey(OptedInBytePrefix, chainID)
```

And for simplicity for each validator we store a boolean on whether this validator has opted in on this chain or not.
```
ChainIdAndConsAddrKey(ValidatorOptedInBytePrefix, chainID, addr)
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
We could technically opt in validators automatically if they voted Yes during the `ConsumerAdditionProposal`. We do not follow this approach and all validators that opt in should send a `MsgOptIn` message. This is because, opting in validators automatically would obfuscate the semantics of proposals. We can envision cases where a validator votes `Yes` for a proposal but might not want to validate or is not ready to validate the consumer chain. Note that if a validator opts in on a consumer chain, the validator cannot opt out immediately as is described later on. Also, because we provide a `MsgOptIn` message for validators that opt in after a `ConsumerAdditionProposal` has passed, it is reasonable to enforce the same interface for all validators that opt in.

### How do validators opt out?
Validators that have opted in on a chain can opt out as well. The opt out is not instantaneous and the validator only opts out after a tunable delay of `X` weeks (e.g., 5 weeks). We introduce the delay in order to inform consumer chains about a certain upcoming validator set change in case they want to use this information to take action (e.g., all validators in an opt in chain decide to opt out).

A validator has send this message to opt out:
```
message MsgInitiateOptOut {
    // the chain id of the consumer chain to opt out from
    string chain_id = 1;
    // the provider address of the validator on Cosmos Hub
    string provider_addr = 2;
}
```
Note the `Initiate` in the name of the message that points to the fact that opting out is not instantaneous. The above should only be called when a consumer chain is actually running. We want to prevent cases where you opt in and then opt out before the chain has even started running.

Another approach for opting out could be the following. A validator just opts out by stopping validating on the consumer chain. If we notice this, then we could opt out the validator if the validator is not in the Top N case. We do not follow this approach because it would slow consumer chains (opted out validators would still become proposers in consensus rounds) and additionally it would make it harder for the consumer chain to know which validators are currently securing it – Is a validator just down or did it fully stop validating it?

Another benefit of introducing a time delay on when the actual opt out takes place is that we prevent a validator from joining and then rejoining multiple times in short bursts. This way we simplify the reward distribution because we know that when we distribute the rewards on the provider chain that a validator that is currently there has actually contributed for some time and deserves rewards.

Finally, a validator could technically opt out automatically by having all the tokens undelegated or redelegated. This is not an issue per se because: i) the validator remains opted in if it joins later on (during the time delay it takes for the opt out to take place), and ii) unbonding tokens need 21 days to unbond and be reused and similarly the number of redelegations is bounded so an adversary with multiple tokens cannot be joining and leaving Opt In chains ad infinitum.

#### State & Query
We store information for each the list of validators that have initiated opt out and update the list accordingly at the beginning of each block.
```
ChainIdAndConsAddrKey(OptedOutBytePrefix, chainID)
```

And for simplicity for each validator we store a boolean on whether this validator has opted out on this chain or not. This also includes information on the exact date the opt out was initiated and when it is going to complete.

```
ChainIdAndConsAddrKey(ValidatorOptedOutBytePrefix, chainID, addr.ToSdkConsAddr())
```

We augment the state of the provider to keep track for each chain all the validators that have opted in.
```
// returns all the validators that have opted out on chain `chainID`
func (k Keeper) GetOptedOutValidators(ctx sdk.Context, chainID string) []validators
```

We also update the state of the opted-in validators when a validator has opted out. We do this check in every `BeginBlock`.

We introduce a query to retrieve the validators that are about to be opted out. The query would operate as follows.
```
gaiad query provider optedOutValidators $chainId
```

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
func (k Keeper) GetPartialSetValidators(ctx types.Context, chainId string valUpdates []abci.ValidatorUpdate) (newUpdates []abci.ValidatorUpdate)

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
Currently, rewards are distributed as follows: The consumer [periodically sends rewards](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/consumer/keeper/distribution.go#L148) on the provider `ConsumerRewardsPool` address. The provider then [transfers those rewards to the fee collector address](https://github.com/cosmos/interchain-security/blob/v3.3.0/x/ccv/provider/keeper/distribution.go#L77) and those transferred rewards are distributed to validators and delegators.

We could use something like `AllocateTokenRewards` but still needs a lot of work because we need to deduce tokens beforehand and so on … Probably doesn’t have to be exact science .. since we already do not distribute exactly.

### Misbehaviour

#### Fraud votes
For fraud votes, we add a new type `FraudVoteProposal` similar to [EquivocationProposal](https://github.com/cosmos/interchain-security/pull/703). The time to detect incorrect execution evidence is 7 days (the same time as that of detecting a light client attack on a client with a `trustingPeriod` of 14 days); We have 7 days to detect an incorrect execution and then 14 days for the proposal to be accepted.

##### When are fraud votes eligible?
Because fraud votes allow the slashing of a validator through a governance proposal, we are cautious on when a fraud vote is eligible and try to restrict their eligibility as much as possible to avoid an adversary proposing a bogus fraud vote. For this, we only consider validators that have opted in in an Opt In chain. Fraud votes are also **only** intended to be used for **malicious** behaviour, for example, in a scenario similar to what [happened to Neutron](https://blog.neutron.org/neutron-halt-post-mortem-927dbe4540c8), validators should vote against slashing those validators.

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
We do not change the way downtime jailing functions. If a validator is down on a consumer chain for an adequate amount of time, we jail this validator on Cosmos Hub.

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
