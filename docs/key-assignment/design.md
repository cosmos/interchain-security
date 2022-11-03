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


### System integration points

There are some integration points with the system

1. `KeyAssignment.ComputeUpdates(..)` in provider `EndBlocker`, during `sendValidatorUpdates`\
The validator updates from the staking module on the provider are transformed by mapping the validator consensus key to their assigned consumer consensus key. If no assignment has been explicitly made, then the provider consensus key is used.
2. `KeyAssignment.PruneUnusedKeys(..)` in provider `OnRecvVSCMaturedPacket`\
On receiving a VSCID for a consumer in a maturity packet, it is certain that any consensus keys which were sent to the consumer at a vscid <= VSCID with a _zero_ power update, and have not since been sent to the consumer with a _positive_ power update, can be pruned, as these keys are no longer
valid for slashing.
3. `KeyAssignment.GetProviderPubKeyFromConsumerConsAddress(..)` in provider `HandleSlashPacket`\
Slash packets delivered to the provider contain the consensus address for the validator to be slashed, as it is known to tendermint on the consumer chain. The consensus address is used as a key in a lookup table to retrieve the _provider_ validator consensus address. This can be then be used to slash the validator accordingly.
4. `KeyAssignment.DeleteProviderKey(..)` in provider staking hook `AfterValidatorRemoved`\
When a validator is entirely removed on the provider chain, the associated index data is deleted from the state.
5. `SetProviderPubKeyToConsumerPubKey(..)` in provider `CreateConsumerClient` during `MakeConsumerGenesis`\
When a new consumer is added, the provider exports a genesis state for that consumer. At this time,
the initial validator set must be computed. It is mapped through the assigned consensus keys, exactly as happens in the provider `EndBlocker` (see bullet 1).
6. `DeleteKeyAssignment(chainID)` in provider `StopConsumerChain`\
When a consumer chain is stopped, all of the associated state is deleted.
7. The internal state is serialized during provider `ExportGenesis`\
Self explanatory.
8. The internal state is loaded during provider `InitGenesis`\
Self explanatory.
9. `AssignConsensusPublicKeyToConsumerChain(..)` TX handler in provider `msg_server`\
A tx type is exposed on the provider, which takes a valid consumer chainID, and a tendermint public key. A validator on the provider must sign the tx. On receipt, the specified public key will
be used to send updates for that validator to the specified consumer chain.
10. `QueryConsumerChainValidatorKeyAssignment(..)` query handler in provider `grpc_query`\
Query the currently assigned tendermint public key for a given (validator, consumer chain) pair.

### Algorithm idea

The bulk of the computation takes place inside the `ComputeUpdates(..)` method of the KeyAssignment instance for a given consumer chain. The method transforms a set of validator updates returned by the provider staking module. It returns a set of validator updates to be sent to the consumer chain (which will be forwarded to tendermint on the consumer) chain. The updates are computed to ensure a consistent replicated validator set on the consumer chain. 

Ensuring a consistent replicated validator set, means that when the assigned key for a given validator changes, an `abci.ValidatorUpdate` with zero power must be sent for the old key and a new update must be sent with the latest power for the new key. 

Here is an _idea_ of the `ComputeUpdates` algorithm:

```
// A per-consumer chain instance of KeyAssignment enables mapping updates from the provider
// to updates for the consumer
ComputeUpdates(vscid VSCID, stakingUpdates []abci.ValidatorUpdate) (consumerUpdates []abci.ValidatorUpdate){

	updatesToSend <- map<key, power>

	// Step 1
	// Get a list of provider consensus keys for which, either,
	// a) the assigned key has changed and the consumer has the old assigned key
    // b) the voting power has changed
	keys <- getProviderKeysForUpdate(stakingUpdates)
	// Step 2
	// For each provider consensus key for which
	// a) the consumer has the old assigned key
	// retrieve the last voting power associated to that key, that the consumer was sent
	// (since the consumer 'has' the old assigned key, the power will be positive)
	lastPositiveUpdates <- getProviderKeysLastPositiveUpdate(keys)
	// Step 3
	// For each provider consensus key for which
	// a) the consumer has the old assigned key
	// note a ZERO power update in updatesToSend.
	// After this step, updatesToSend contains a zero power update for
	// each consensus key that the consumer chain tendermint instance is aware of.
	// In this manner, these updates, when handed to tendermint, DELETE the validator
	// from the active set.
	for key in keys {
		if there is an update in lastPositiveUpdates for key {
			updatesToSend[consumerKey(key)] <- 0
		}
	}
	// Step 4
	// For each provider consensus key for which
	// a) the assigned key has changed and the consumer has the old assigned key
    // b) the voting power has changed
	// If the voting power changed, create an update for that key with the latest
	// voting power. If the voting power did not change, create an update for that
	// key with the LAST voting power associated to that key.
	for key in keys {
		power <- 0
		if there is an update in lastPositiveUpdates for key {
			power <- update.power
		}
		if there is an update in stakingUpdates for key {
			power <- update.power
		}
		if 0 < power {
			updatesToSend[consumerKey(key)] <- power
		}
	}

	// Step 5
	for <key, power> in updatesToSend {
		if 0 < power {
			// Store the update, so that it will be retrieved in future calls to
			// getProviderKeysLastPositiveUpdate(..)
		}
	}

	return mapToList(updatesToSend)
}
```

TODO: pruning, slash lookup, key assign

## External properties

KeyAssignment has some properties relevant to the external user:


1. Validator Set Replication\
   When the Interchain Security property [Validator Set Replication](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties) holds for an implementation without KeyAssignment, then the property holds when KeyAssignment is used.
2. Slashable Consumer Misbehavior\
   When the Interchain Security property [Slashable Consumer Misbehavior](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties) holds for an implementation without KeyAssignment, then the property holds when KeyAssignment is used.

All Interchain Security properties still hold when KeyAssignment is used, the above are just the most relevant.

Additionally

3. Timeliness\
When a `AssignConsensusPublicKeyToConsumerChain` operation succeeds for a given `(chainID, ProviderValidatorAddress, ConsumerConsensusPubKey)` tuple at block height `hp0`, and is not followed by a subsequent call for a tuple starting `(chainID, ProviderValidatorAddress,)` before or during a height `hp1` (`hp0 <= hp1`), and at `hp1` a validator set update packet is committed at the provider chain, then at the next earliest height `hc2` on the consumer chain that the packet committed at `hp1` is received, the key `ConsumerConsensusPubKey ` is passed as consensus key to tendermint. Thus tendermint will expect a signature from `ConsumerConsensusPubKey ` from height `hc2 + 1`.


## Internal properties

The internal properties section in [api.tla](./api.tla) specifies abstract but precise properties. In particular, at a high level:

1. The consumer validator set is always defined as per the validator set replication property.
2. It is always possible to lookup the provider consensus address, for a given consumer consensus public key, when the consumer has been sent that public key and that key is still liable for double signing or downtime slashing.
3. The storage requirements are reasonable.

Please see [api.tla](./api.tla) and [key_assignment_test.go::externalInvariants](../../x/ccv/provider/keeper/key_assignment_test.go) and [key_assignment.go::internalInvariants](../../x/ccv/provider/keeper/key_assignment.go) for precise formulations.
