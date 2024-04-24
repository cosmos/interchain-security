# ADR 016: CosmoLayer

## Changelog

-  2024-04-24: Initial draft of ADR

## Status

Draft

## Context

CosmoLayer enables staking of tokens from external sources such as Ethereum or Bitcoin to Cosmos blockchains. By integrating CosmoLayer, a Cosmos blockchain can be secured by staked Ethereum and native tokens.

CosmoLayer solution consists of 4 parts

- External staking solution such as Babylon or EigenLayer AVS contract
- Oracle (tracks how much ETH has been delegated to each validator and provides price feeds for external tokens)
- CosmoLayer: Cosmos modules (combines external and native stakes to derive power of each validator)
- Bridge to EigenLayer (needed for rewards to be sent back to EigenLayer)

External staking information is received from an oracle together with price information of related stakes.
The CosmosLayer derives validator powers based on external and native staking information and initiates rewarding of external depositors.

Present ADR describes the _Cosmos modules_ of the solution.

## Alternative Approaches

> This section contains information around alternative options that are considered
> before making a decision. It should contain a explanation on why the alternative
> approach(es) were not chosen.


## Decision

> This section records the decision that was made.
> It is best to record as much info as possible from the discussion that happened.
> This aids in not having to go back to the Pull Request to get the needed information.

## Detailed Design

The Cosmos modules are an integral part of the CosmoLayer solution and consist of a `Power Mixing` and a `Reward Handler` module.
The `Power Mixing` module provides the capability of deriving validator power based on stake originated from external sources such as Ethereum/Bitcoin and the native staking module.
The `Reward Handler` is in charge of sending rewards to external stakers.

### Power Mixing

Power Mixing provides the final validator powers based on staking information of the native chain and the external stakes e.g. from Ethereum EigenLayer. The information about external staking and related price feeds are received from `Slinky Oracle`.
Once the final validator powers are determined the result is submitted to the underlying CometBFT consensus layer by [updating](https://docs.cometbft.com/v0.38/spec/abci/abci++_app_requirements#updating-the-validator-set) the validator set.

Requirements:

- validator updates are performed on each EndBlock
- a validator's power is determined based on its native on-chain stakes and external stakes
- price information of staked tokens is used to determine a validator’s power, e.g. price ratio (price of native on-chain token / price of external stake)
- price information of native/external tokens are received from `[Slinky Oracle](https://www.notion.so/informalsystems/02-cosmolayer-oracle.md)`
- staking information of EigenLayer are received from the `Slinky Oracle`
- staking information of Bitcoin are received from Babylon's Bitcoin staking protocol
- native staking information are received from the `Cosmos SDK Staking Module`
- set of validator stakes from `Slinky Oracle` always have the current price, full set of validators, and current stakes

The `Power Mixing` implementation
- queries current validators from [x/staking](https://github.com/cosmos/cosmos-sdk/blob/a6f3fbfbeb7ea94bda6369a7163a523e118a123c/x/staking/types/staking.pb.go#L415)
and from `Slinky Oracle` (see below).
- determines validator power from local and external staked validator sets
- updates validator set on cometBFT ABCI (x/staking is doing this in ValidatorUpdates 'values are overwritten in every block', ICS provider module intervenes in this behavior during `EndBlock`)

### Queries

The following queries will be provided by `Slinky Oracle` (extension to current implementation)

```protobuf
service Query {
    rpc GetExtValidators(GetExtValidatorRequest) returns (ExtValidatorsResponse) {
         option (google.api.http).get = "/slinky/oracle/v1/get_validators";
    };
}

message GetExtValidatorRequest {}

// ExtValidatorsResponse is the response from GetExtValidators queries
message ExtValidatorsResponse {
  repeated ExtValPower powers;
}

// ExtValPower represents a validator with its staking and token information,
// where `stakes` is the total amount of stakes for a validator and `denom` is the
// source token of the stake e.g. ETH,BTC.g
message ExtValPower {
  string validator_address;
  uint64 stakes;
  string denom;
}

```

current implementation of `Slinky Oracle` provides a query [GetPrice](https://github.com/skip-mev/slinky/blob/main/proto/slinky/oracle/v1/query.proto)
to get the latest price feed for a currency pair.

```protobuf
service Query {
  rpc GetPrice(GetPriceRequest) returns (GetPriceResponse) {
    option (google.api.http).get = "/slinky/oracle/v1/get_price";
  };
}
```

For security reasons the amount of external stakes needs to be limited. Limitation of external staking will be driven by a `Governance Proposal`.

### Reward Handler

For native staked tokens the `Distribution Module` of the Cosmos SDK is taking care of sending the rewards to stakers.
For stakes originated from external chains (Ethereum/Bitcoin) the `Reward Handler` module sends rewards to EigenLayer/Babylon.
The transfer of rewards is done using a [bridge](https://ethereum.org/en/bridges/) between the Cosmos chain and Eigenlayer/Babylon.

Note: currently there's no support paying rewards on EigenLayer (see [here](https://www.coindesk.com/tech/2024/04/10/eigenlayer-cryptos-biggest-project-launch-this-year-is-still-missing-crucial-functionality/))

## Consequences

> This section describes the consequences, after applying the decision. All
> consequences should be summarized here, not just the "positive" ones.

### Positive

* Allow external depositors to stake their tokens to secure a Cosmos chain

### Negative
* Dependency to external sources e.g (price feeds) for validator power calculation
* Security impact

### Neutral
* Additional complexity for staking

## Questions:

- Determinism of the price feed? → yes, but capability of backtracking how a price was determined by `Slinky Oracle` needs to be checked (TODO)
- Slashing: subject of this ADR? (Defined but [not activated](https://www.coindesk.com/tech/2024/04/10/eigenlayer-cryptos-biggest-project-launch-this-year-is-still-missing-crucial-functionality/) currently on EigenLayer).

## References

> Are there any relevant PR comments, issues that led up to this, or articles
> referenced for why we made the given design choice? If so link them here!

- [Slinky Oracle](https://github.com/skip-mev/slinky)
- [EigenLayer](https://docs.eigenlayer.xyz/)
- [Babylon](https://babylonchain.io/)
