# ADR 016: CosmoLayer

## Changelog

-  2024-04-05: Initial draft of ADR

## Status

Draft

## Context

> This section contains all the context one needs to understand the current state,
> and why there is a problem. It should be as succinct as possible and introduce
> the high level idea behind the solution.

CosmoLayer enables re-staking of Ethereum tokens to Cosmos blockchains. By integrating CosmoLayer, a Cosmos blockchain can be secured by staked Ethereum and native tokens.

CosmoLayer is based on 4 parts

- EigenLayer AVS contract (restaking, slashing of validators)
- Oracle (tracks how much ETH has been delegated to each validator)
- Cosmos modules (combines external and native stakes to derive power of each validator)
- Bridge to EigenLayer (needed for rewards to be sent back to EigenLayer)
where each part is described by its own ADR.

Present [ADR](01-cosmolayer-cosmos_module.md) describes the Cosmos modules of the solution.

```
- Any Cosmos blockchain can deploy an EigenLayer AVS

- An EigenLayer allows Ethereum stakers to restake their Eth and other tokens to other systems (Cosmos chains)`
```

## Alternative Approaches

> This section contains information around alternative options that are considered
> before making a decision. It should contain a explanation on why the alternative
> approach(es) were not chosen.

### Reward Distribution

1. External stakers rewarded with native cosmos-chain tokens
    - No channel back to source of stakes (EigenLayer/Babylon) needed.
    - Stakers are not rewarded in form of 'source' tokens
    - Transfer of the rewards back to external stake is up to the user
    - All external staker addresses need to be sent to cosmos chain
    - External stakers need to have an address on th cosmos chain where their external staking address is mapped against
2. External stakers rewarded with source stakes (EigenLayer/Babylon)
This can be realized by a bridge transfering back rewards to stakers on Eigenlayer,
wich requires
    - a pool of tokens - with sufficient size - on EigenLayer to distribute rewards to Ethereum stakers.
    - complex (distribution logic/contract on Eigenlayer/Babylon)
    - bridge can be implemented by `Slinky Oracle` module or on cosmos-chain


## Decision

> This section records the decision that was made.
> It is best to record as much info as possible from the discussion that happened.
> This aids in not having to go back to the Pull Request to get the needed information.

## Detailed Design
> This section does not need to be filled in at the start of the ADR, but must
> be completed prior to the merging of the implementation.
>
> Here are some common questions that get answered as part of the detailed design:
>
> - What are the user requirements?
>
> - What systems will be affected?
>
> - What new data structures are needed, what data structures will be changed?
>
> - What new APIs will be needed, what APIs will be changed?
>
> - What are the efficiency considerations (time/space)?
>
> - What are the expected access patterns (load/throughput)?
>
> - Are there any logging, monitoring or observability needs?
>
> - Are there any security considerations?
>
> - Are there any privacy considerations?
>
> - How will the changes be tested?
>
> - If the change is large, how will the changes be broken up for ease of review?
>
> - Will these changes require a breaking (major) release?
>
> - Does this change require coordination with the SDK or other?


-----
The `Cosmos Modules` are an integral part of the CosmoLayer solution and consist of a `Power Mixing` and a `Reward Handler` module.
The `Power Mixing` module provides the capability of deriving validator power based on stake originated from Ethereum and the native staking module.
The `Reward Handler` is in charge of sending rewards to external stakers on Ethereum EigenLayer.

---

### Power Mixing

Power Mixing provides the final validator powers based on staking information of the native chain and the external stakes e.g. from Ethereum EigenLayer. The information about external staking and related price feeds are received from `Slinky Oracle`.
Once the final validator powers are determined the result is submitted to the underlying CometBFT consensus layer by [updating](https://docs.cometbft.com/v0.38/spec/abci/abci++_app_requirements#updating-the-validator-set) the validator set.

Requirements:

- validator updates are performed on each EndBlock
- a validator's power is determined based on its native on-chain stakes and external stakes
- price information of staked tokens is used to determine a validator’s power, e.g. price ratio (price of native on-chain token / price of external stake)
- price information of native/external tokens are received from the `[Slinky Oracle](https://www.notion.so/informalsystems/02-cosmolayer-oracle.md)`
- external staking information are received from the `Slinky Oracle`
- native staking information are received from the `Cosmos SDK Staking Module`
- Set of validator stakes from `Slinky Oracle` always have the current price, full set of validators, and current stakes

The `Power Mixing` module implements:

- `UpdateValidatorSet()`
queries current Validators from [x/staking](https://github.com/cosmos/cosmos-sdk/blob/a6f3fbfbeb7ea94bda6369a7163a523e118a123c/x/staking/types/staking.pb.go#L415)
queries current validatorset from oracle (see below)
powerMix() determines validator power from local and external staked validator sets
update validator set on cometBFT ABCI (x/staking is doing this in ValidatorUpdates 'values are overwritten in every block', ICS provider module intervenes in this behaviour during `EndBlock`)

### Queries

The following queries will be provided by `Slinky Oracle` (extension to current implementation)

```protobuf
message ExtValidatorUpdates {
  repeated ExtValPower powers;
  PriceUpdate price;
}

message ExtValPower {
  string validator_address;
  uint64 stakes;
}

// TBD if this is needed
message GetExtDelegators {
	string eth_address;
	uint64 stakes;
}
```

```protobuf
message PriceUpdate {
  float ratio;
  string denom;
}
```

### Questions:

- When are validator powers re-calculated (price update)?
Event based from `oracle` [price triggerd] / interval?
→ Reqular updates e.g. next epoch
- How does 'Unbonding' work for ETH stake?
(TokenManager on Eigenlayer. TBD if unbonding period on Eigenlayer match with cosmos-chain [bootstrapping/setup] is a requirement)
- What are the external delegator addresses used for?
Only needed if rewards are issued locally?
- Are thre any ICS dependencies to be considered?
- Determinims of the validator powers ? → deterministic due to extended votes
- Determinism of the price feed? → yes but capability of backtracking how a price was determined by `Slinky Oracle` needs to be checked (TODO)
- Slashing: double signing evidence?

### Alternative Solution

- Oracle provides only price feeds and external validator stakes are received by a bridge to AVS

---

### Reward Handler

For native staked tokens the `Distribution Module` of the Cosmos SDK is taking care of sending the rewards to stakers.
For stakes originated from Ethereum the `Reward Handler` module sends rewards to the AVS contract of the related Cosmos chain.
The transfer of rewards is done using a [bridge](https://ethereum.org/en/bridges/) between the Cosmos chain and Ethereum Eigenlayer.

**Alternative Solution**

1. the `Reward Handler` sends rewards to the related Eigenlayer AVS of the chain via `Slinky Oracle` which establish a bridge to Ethereum.
2. the `Reward Handler` issues rewards for external staker to their address on the Cosmos chain.
This requires:
    1. sending all external stakers to cosmos chain
    2. mapping of restaker addresses to their registered addresses on cosmos chain


## Consequences

> This section describes the consequences, after applying the decision. All
> consequences should be summarized here, not just the "positive" ones.

### Positive

* Allow Ethereum stakers to re-stake their tokens to secure a Cosmos chain

### Negative

* Additional complexity for staking
* Depenency to external sources e.g (price feeds) for validator power calculation
* backtracking of price feeds at a certain point in time

### Neutral


## References

> Are there any relevant PR comments, issues that led up to this, or articles
> referenced for why we made the given design choice? If so link them here!

- [Cosmolayer - Oracle](./02-cosmolayer-oracle.md)
- {reference link}
