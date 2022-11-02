# KeyAssignment

KeyAssignment is the name of the feature that allows validator operators to use different consensus keys for each consumer chain validator node that they operate.

Validators can improve their security by using different consensus keys for each chain. That way, different teams in an organization can operate a subset (can be size 1) of the total number of consumer chains associated to a provider chain. If one key leaks the other keys will not be at risk. It is possible to change the keys at any time by submitting a transaction.

## Overview

The KeyAssignment feature is available via a provider chain API (transactions and queries). The provider chain validator operator submits an assignment transaction to the provider chain with a consumer chain ID and desired consensus key as parameters. The over-IBC protocol used by Interchain Security takes care of forwarding the assignment to the specified consumer chain. When the consumer chain receives the key, it will immediately start using it with tendermint.

It is possible to start validating a consumer chain with the same key as used for the provider. This is the default behavior. It is also possible to specify another key to use when joining the validator set. Moreover it is possible to change the used key at any time, any multiple times, with some minor restrictions.

## External API (High Level)

**TXs**

```go
// Assign a new public consensus key to be used by a validator
// on the provider when it signs transactions on the consumer chain.
// The TX must be signed by the private key associated to the provider
// validator address.
//
// The assignment can fail if the consumer consensus key is already
// in use for the chain, currently, or in the recent past.
AssignConsensusPublicKeyToConsumerChain(
	ChainId                  string, // consumer chain
	ProviderValidatorAddress string, // must sign TX
	ConsumerConsensusPubKey  *types.Any
)
```

**Queries**

```go
// Returns the last consumer key associated to the provider key and
// the consumer chain by a call to AssignConsensusPublicKeyToConsumerChain.
QueryConsumerChainValidatorKeyAssignment (
	ChainId                  string, // consumer chain
	ProviderValidatorAddress string, // validator address for the provider chain
)
```

## Internal API (High Level)

TODO: write this section.

## API (Details)

The external API is specified in [api.tla](./api.tla). An 'internal' API is also specified. The external API supports the TXs and Queries listed above. The internal API documents the API that the implementation of KeyAssignment exposes for integration
in the implementation of the wider system.

## Implementation

### Algorithm idea


### System integration points


## External properties

KeyAssignment has some properties relevant to the external user:



1. Validator Set Replication\
   When the Interchain Security property [Validator Set Replication](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties) holds for an implementation without KeyAssignment, then the property holds when KeyAssignment is used.
2. Slashable Consumer Misbehavior\
   When the Interchain Security property [Slashable Consumer Misbehavior](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties) holds for an implementation without KeyAssignment, then the property holds when KeyAssignment is used.

All Interchain Security properties still hold when KeyAssignment is used, the above are just the most relevant.

Additionally

3. When a `AssignConsensusPublicKeyToConsumerChain` operation succeeds for a given `(chainID, ProviderValidatorAddress, ConsumerConsensusPubKey)` tuple at block height `hp0`, and is not followed by a subsquent call for the same tuple before or during a height `hp1` (`hp0 <= hp1`), and at `hp1` a validator set update packet is committed at the provider chain, then at the next earliest height `hc2` on the consumer chain that the packet is received, the `ConsumerConsensusPubKey ` is passed as consensus key to tendermint. Thus tendermint will expect a signature from `ConsumerConsensusPubKey ` from height `hc2 + 1`.


## Internal properties

The internal properties section in [api.tla](./api.tla) specifies abstract but precise properties. In particular, at a high level:

1. The consumer validator set is always defined as per the validator set replication property.
2. It is always possible to lookup the provider consensus address, for a given consumer consensus public key, when the consumer has been sent that public key and that key is still liable for double signing or downtime slashing.
3. The storage requirements are reasonable.

Please see [api.tla](./api.tla) and [key_assignment_test.go::externalInvariants](../../x/ccv/provider/keeper/key_assignment_test.go) and [key_assignment.go::internalInvariants](../../x/ccv/provider/keeper/key_assignment.go) for precise formulations.
