---
sidebar_position: 17
title: Security aggregation
---
# ADR 016: Security aggregation

## Changelog

-  2024-04-24: Initial draft of ADR

## Status

Proposed

## Context

Security Aggregation enables staking of tokens from external sources such as Ethereum or Bitcoin to Cosmos blockchains. By integrating Security Aggregation, a Cosmos blockchain can be secured by both native tokens and external tokens (e.g. ETH, BTC).

Security Aggregation consists of the following parts:

- A mechanism for delegating external tokens to Cosmos validators, such as Babylon or EigenLayer AVS contract.
- An oracle that tracks how much external stake has been delegated to each Cosmos validator and provides price feeds for external tokens.
- Power mixing:  a mechanism to combine external and native stake to derive the power of each validator.
- A reward distribution protocol that enables sending back rewards to the external source.

External staking information is received from an oracle together with price information of related stakes.
The CosmosLayer derives validator powers based on external and native staking information and initiates rewarding of external depositors.

This ADR describes the _Cosmos modules_ of the solution.

## Alternative Approaches

### Rewards
As an alternative to sending rewards back to the external chains, stakers could be rewarded on the Cosmos chain.
This would require a mapping of external addresses to addresses on Cosmos chain for each staker on external source.
In addition detailed external staking information such as staking addresses, amount of stakes per staker and validator, etc. have to be provided by the oracle.

## Decision

### Rewards will be sent back to external chains instead of paying rewards for external stakers on Cosmos chain
Rewards will be sent back to external chains instead of paying rewards for external stakers on Cosmos chain
- due to amount of additional staking information to be sent and tracked by the oracle
- due to the additional complexity of managing external and Cosmos addresses

## Detailed Design

The `Power Mixing` feature and `Reward Distribution` protocol are an integral part of the Security Aggregation solution.
The `Power Mixing` module provides the capability of deriving validator power based on stake originated from external sources such as Ethereum/Bitcoin and the native staking module.
The `Reward Distribution` manages the process of sending rewards to external stakers.

### Power Mixing

Power Mixing provides the final validator powers based on staking information of the native chain and the external stakes. The information about external staking and related price feeds are received from an oracle.
Once the final validator powers are determined the result is submitted to the underlying CometBFT consensus layer by [updating](https://docs.cometbft.com/v0.38/spec/abci/abci++_app_requirements#updating-the-validator-set) the validator set.

Requirements:

- validator updates are performed on each EndBlock
- a validator's power is determined based on its native on-chain stakes and external stakes
- price information of staked tokens is used to determine a validator’s power, e.g. price ratio (price of native on-chain token / price of external stake)
- price information of native/external tokens are received from an oracle
- staking information from external sources received from the oracle
- native staking information are received from the `Cosmos SDK Staking Module`
- set of validator stakes from oracle always have the current price, full set of validators, and current stakes

The `Power Mixing` implementation
- queries current validators and their powers from [x/staking](https://github.com/cosmos/cosmos-sdk/blob/a6f3fbfbeb7ea94bda6369a7163a523e118a123c/x/staking/types/staking.pb.go#L415)
and from oracle (see below).
- calculates power updates by mixing power values of external and internal sources
Following pseudocode snippet shows a possible implementation of how power mixing
feature works.
```golang
// PowerSource is an abstract entity providing validator powers which
// are used by the mixer. This can be an oracle, staking module or an
// IBC connected bridge.
type PowerSource interface {
  GetValidatorUpdates() []abci.ValidatorUpdate
}

// MixPowers calculates power updates by mixing validator powers from different sources
func (k *Keeper) MixPowers(source ...PowerSource) []abci.ValidatorUpdate {
  var valUpdate []abci.ValidatorUpdate
  for _, ps := range source {
    // mix powers from two sets of validator updates an return set of validator updates
    // with aggregated powers
    valUpdate = mixPower(valUpdate, ps.GetValidatorUpdates())
  }
  return valUpdate
}

func (k *keeper) EndBlock(ctx sdk.Context, _ abci.RequestEndBlock) []abci.ValidatorUpdate {
  // GetPowerSources (including local staking module)
  registeredPowerSource := GetPowerSources()
  return k.MixPowers(registeredPowerSource...)
}
```

#### Integration with `ICS provider`
The provider module updates the validator set on CometBFT instead of the SDK staking module (x/staking). The provider implementation will intervene in this behavior and ensure that the validator updates are taken from the `Power Mixing` feature.

External power sources are managed by the provider module. Only registered power sources can provide input to the `Power Mixing` feature.
Power sources will be assigned a unique identifier which will be used by the oracle, provider module and the power mixing and rewarding feature.

Updates with the next validator set are sent to consumer chains on each epoch (see `EndBlockVSU()`).
When collecting the validator updates for each consumer chain (see [`QueueVSCPackets()`](https://pkg.go.dev/github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper#Keeper.QueueVSCPackets)), the validator powers of the bonded validators will be updated with the validator powers from the external sources using the `Power Mixing` module.
These updates are sent as part of the VSC packets to all registered consumer chains.

#### Integration with `ICS consumer`
Consumer chains receive validator updates as part of VSC packets from the provider.
These packets contain validator powers which were already mixed with external staked powers.


### Queries

```protobuf
// GetValidatorUpdates returns the power mixed validator results from the provided sources
service Query {
  rpc GetValidatorUpdates(PowerMixedValUpdateRequest) PowerMixedValUpdateResponse {};
}

// PowerMixedValUpdateRequest contains the list of power sources on which the
// power mixing should be based on
message PowerMixedValUpdateRequest {
  repeated PowerSource sources;
}

// PowerMixedValUpdateResponse returns the validator set with the updated powers
// from the power mixing feature
message PowerMixedValUpdateResponse {
  repeated abci.ValidatorUpdate val_set
}
```


The following queries will be provided by the oracle

```protobuf
service Query {
    rpc GetExtValidators(GetExtValidatorRequest) returns (ExtValidatorsResponse) {
         option (google.api.http).get = "oracle/v1/get_validators";
    };
}

message GetExtValidatorRequest {}

// ExtValidatorsResponse is the response from GetExtValidators queries
message ExtValidatorsResponse {
  repeated ExtValPower powers;
}

// ExtValPower represents a validator with its staking and token information,
// where:
// `power_source_identifier` is the identifier of the registered power source
// `validator_address` is the address of the validator
// `stakes` is the total amount of stakes for a validator
// `denom` is the source token of the stake e.g. ETH,BTC
// `price_ratio` is the ratio of price of the external token to the price of the 'local' token
message ExtValPower {
  string power_source_identifier;
  string validator_address;
  uint64 stakes;
  string denom;
  float  price_ratio;
}

// GetPrice returns a price feed for a given token
service Query {
  rpc GetPrice(GetPriceRequest) returns (GetPriceResponse) {
    option (google.api.http).get = "/oracle/v1/get_price";
  };
}
```

For security reasons the amount of external stakes needs to be limited. Limitation of external staking could be driven by governance and is not subject of this version of the ADR.

### Reward Handler

For native staked tokens the `Distribution Module` of the Cosmos SDK is taking care of sending the rewards to stakers.
For stakes originated from external chains (Ethereum/Bitcoin) the `Reward Handler` module sends rewards to EigenLayer/Babylon.
The transfer of rewards is done using a bridge between the Cosmos chain and the external provider chain.

Note: currently there's no support paying rewards on EigenLayer (see [here](https://www.coindesk.com/tech/2024/04/10/eigenlayer-cryptos-biggest-project-launch-this-year-is-still-missing-crucial-functionality/))

## Consequences

### Positive

* Allow external depositors to stake their tokens to secure a Cosmos chain

### Negative
* Dependency to external sources e.g (price feeds) for validator power calculation
* Security impact

### Neutral
* Additional complexity for staking

## Questions:
- Slashing: subject of this ADR? (Defined but [not activated](https://www.coindesk.com/tech/2024/04/10/eigenlayer-cryptos-biggest-project-launch-this-year-is-still-missing-crucial-functionality/) currently on EigenLayer).

## References

- [EigenLayer](https://docs.eigenlayer.xyz/)
- [Babylon](https://babylonchain.io/)
