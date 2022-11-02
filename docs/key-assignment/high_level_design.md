# KeyAssignment

KeyAssignment is the name of the feature that allows validator operators to use different consensus keys for each consumer chain validator node that they operate.

Validators can improve their security by using different consensus keys for each chain. That way, different teams in an organization can operate a subset (can be size 1) of the total number of consumer chains associated to a provider chain. If one key leaks the other keys will not be at risk. It is possible to change the keys at any time by submitting a transaction.

## Overview

The KeyAssignment feature is available via a provider chain API (transactions and queries). The provider chain validator operator submits a mapping transaction to the provider chain with a consumer chain ID and desired consensus key as parameters. The IBC protocol used by Interchain Security takes care of forwarding the mapping to the specified consumer chain. When the consumer chain receives the key, it will immediately start using it with tendermint.

It is possible to start validating a consumer chain with the same key as used for the provider. It is also possible to specify another key to use when joining the validator set. Moreover it is possible to change the used key at any time, any multiple times, with some minor restrictions.

## API (High level)

**Writes**

```go
// Associates a new consumer key as consensus key on the consumer chain
// for the validator on the provider chain associated to the provider key.
SetConsumerKey(providerKey, consumerChainID, consumerKey) {
}
```

**Reads**

```go
// Returns the last consumerKey associated to the provider key and
// the consumer chain by a call to SetConsumerKey.
GetConsumerKey(providerKey, consumerChainID) {
}
```

```go
// Returns the last providerKey associated to consumerKey and the consumer
// chain by a call to SetConsumerKey.
GetProviderKey(consumerKey, consumerChainID) {
}
```

## API (Details)

**Writes**

```go
// Attemps to associate a new consumer key consumerKey on the consumer chain
// specified by consumerChainID to the validator on the provider chain
// specified by providerKey.
// If the attempt succeeds, the consumer chain will start consumerKey as
// consensus key from the earliest block at which it receives the update
// via IBC.
// The attempt can fail if any of the arguments are invalid, if either chain
// or the IBC connection is faulty.
// The attempt can additionally fail if the key consumerKey was already used
// as for a mapping with the KeyAssignment feature too recently in the past. This is
// to prevent attacks. In particular, once a key is used in a KeyAssignment association
// that key is no longer useable for another association until the first
// association is cancelled, and an acknowledgement of the cancellation is
// received from the consumer chain and processed on the provider chain.
SetConsumerKey(providerKey, consumerChainID, consumerKey) {
    // TODO: signatures, types
}
```

**Reads**

```go
// Returns the last consumerKey associated to the provider key and
// the consumer chain by a call to SetConsumerKey.
// TODO: more detail needed?
GetConsumerKey(providerKey, consumerChainID) {
}
```

```go
// Returns the last providerKey associated to consumerKey and the consumer
// chain by a call to SetConsumerKey.
// TODO: more detail needed?
GetProviderKey(consumerKey, consumerChainID) {
}
```

### External Properties - Interchain Security

KeyAssignment has some properties relevant to the external user

1. Validator Set Replication\
   When the Interchain Security property [Validator Set Replication](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties) holds for an implementation without KeyAssignment, then the property holds when KeyAssignment is used.
2. Slashable Consumer Misbehavior\
   When the Interchain Security property [Slashable Consumer Misbehavior](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties) holds for an implementation without KeyAssignment, then the property holds when KeyAssignment is used.

In fact, all Interchain Security properties still hold when KeyAssignment is used, the above are just the most relevant.

### External Properties - timeliness

When a call to `SetConsumerKey` succeeds for a given `(providerKey, consumerChainID)` tuple at block height `hp0`, and is not followed by a subsquent call for the same tuple before or during a height `hp1` (`hp0 <= hp1`), and at `hp1` a validator set update packet is committed at the provider chain, then at the next earliest height `hc2` on the consumer chain that the packet is received, the `consumerKey` is passed as consensus key to tendermint. Thus tendermint will expect a signature from `consumerKey` from height `hc2 + 1`.

TODO: check, test, correct, guarantee and formalize this.

### Internal properties

The KeyAssignment implementation satisfies a number of internal properties, which are used to guarantee the external properties. These are only relevant to system internals. They are, briefly:

1. Validator Set Replication\
   'All consumer validator sets are some earlier provider validator set'
2. Queries\
   'It is always possible to query the provider key for a given consumer key, when the consumer can still make slash requests'
3. Pruning\
   'When the pruning method is used correctly, the internal state of the data structure does not grow unboundedly'

Details can be found in x/ccv/provider/keeper/keyassignment_core_test.go. TODO: link?
