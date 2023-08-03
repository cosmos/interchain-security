---
sidebar_position: 4
title: Cryptographic verification of equivocation evidence
---
# ADR 005: Cryptographic verification of equivocation evidence

## Changelog
* 5/1/2023: First draft
* 7/23/23: Add light client attacks handling

## Status

Proposed

## Context

Currently, we use a governance proposal to slash validators for equivocation (double signing and light client attacks). This has the downside that it takes 2 weeks for the proposal to be approved, effectively reducing the unbonding period in some respects. This does not lead to any pressing real-world security concerns, but since it involves the basis of proof of stake, it would be good to get consumer chain slashing back to parity as soon as possible.

This ADR proposes a system to slash validators automatically for equivocation, immediately upon the provider chain's receipt of the evidence. Another thing to note is that we intend to introduce this system in stages, since even the partial ability to slash and/or tombstone is a strict improvement in security.
For the first stage of this work, we will only handle light client attacks.

### Light Client Attack

In a nutshell, the light client is a process that solely verifies a specific state machine's
consensus without executing the transactions. The light clients get new headers by querying
multiple nodes, called primary and witness nodes. 

Headers can be verified in two ways: sequentially, where verification occurs in order of block height,
and each new header must be signed by ⅔+ of the voting power from the last trusted header validators;
or using skipping, where intermediate headers are verified and must be signed by ⅓+ of the voting power
from the last trusted header validators. The latter is the default method, as it is faster in most cases.
Additionally, light clients are cross-checking new headers obtained from a primary with witnesses to ensure all nodes share the same state.

A light client attack occurs when a Byzantine validator sends invalid headers to a light client.
As the light client doesn't execute transactions, it can be deceived into trusting corrupted application state transitions.
For instance, if a light client receives header `A` from the primary and header `B` from a witness for the same block height `H`,
and both headers are successfully verified, it indicates a light client attack.
Note that it this case, either the primary and/or witness nodes are malicious.

To orchestrate a light client attack, Byzantine actors create a header with incorrect state transitions that must be signed by ⅓+ of the voting power.
The types of light client attacks are defined by analyzing the differences between the conflicting headers.
If at least one deterministic states isn't equal, i.e. a state resulting from a previous block
(see [CometBFT spec.](https://github.com/cometbft/cometbft/blob/main/spec/core/data_structures.md#header)),
it is referred to a “lunatic attack”. Conversely, in the opposite case, it is termed an “equivocation”, (see [CometBFT spec](https://github.com/cometbft/cometbft/blob/main/spec/light-client/detection/detection_003_reviewed.md)).

When a light client agent detects two conflicting headers, it will initially verify their traces (see [cometBFT detector](https://github.com/cometbft/cometbft/blob/2af25aea6cfe6ac4ddac40ceddfb8c8eee17d0e6/light/detector.go#L28)) using its primary and witness nodes.
If these headers pass successful verification, the Byzantine validators will be identified based on the header's commit signatures
and the type of light client attack. The agent will then transmit this information to its nodes using a [`LightClientAttackEvidence`](https://github.com/cometbft/cometbft/blob/feed0ddf564e113a840c4678505601256b93a8bc/docs/architecture/adr-047-handling-evidence-from-light-client.md) to be eventually voted and committed it to a block. In this scenario, the chain's evidence module will execute the jailing and the slashing of the validators responsible for the light client attack.

Light clients are a core component of IBC.  
In the event of a light client attack, IBC relayers notify the affected chains by submitting an [IBC misbehavior message]((https://github.com/cosmos/ibc-go/blob/2b7c969066fbcb18f90c7f5bd256439ca12535c7/proto/ibc/lightclients/tendermint/v1/tendermint.proto#L79)).
A misbehavior message includes the conflicting headers that constitute a `LightClientAttackEvidence`. Upon receiving such a message,
a chain will first verify whether these headers would have convinced its light client. This verification is achieved by checking
the header states against the light client consensus states (see [IBC misbehaviour handler](https://github.com/cosmos/ibc-go/blob/2b7c969066fbcb18f90c7f5bd256439ca12535c7/modules/light-clients/07-tendermint/types/misbehaviour_handle.go#L101)). If the misbehaviour is successfully verified, the chain will then "freeze" the
light client, halting any further trust in or updating of its states.


## Decision

In the first iteration of the feature, we will introduce a new endpoint: `HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour)`.
The main idea is to leverage the current IBC misbehaviour handling and update it to solely jail and slash the validators that
performed a light client attack. This update will be made under the assumption that the chains connected via this light client
share the same validator set, as it is the case with Replicated Security. 

This endpoint will reuse the IBC client libraries to verify that the misbehaviour headers would have fool the light client.
Additionally, it’s crucial that the endpoint logic result in the slashing and jailing of validators under the same conditions
as a light client agent detector. Therefore, the endpoint will ensure that the two conditions are met:
the headers in the misbehaviour message have the same block height, and
the light client isn’t expired.

After having successfully verified a misbehaviour, the endpoint will execute the jailing and slashing of the malicious validators similarly as in the evidence module (TODO: code ref). 

### Current limitations:

- This only handles light client attacks, not double signing. In the future, we will add the code to also verify double signing.

- We cannot derive an infraction height from the evidence, so it is only possible to tombstone validators, not actually slash them.
To explain the technical reasons behind this limitation, let's recap the initial consumer initiated slashing logic.
In a nutshell, consumer heights are mapped to provider heights through VSCPackets, namely through the so called vscIDs.
When an infraction occurs on the consumer, a SlashPacket containing the vscID obtained from mapping the consumer infraction height
is sent to the provider. Upon receiving the packet, the provider maps the consumer infraction height to a local infraction height,
which is used to slash the misbehaving validator. In the context of untrusted consumer chains, all their states, including vscIDs,
could be corrupted and the ore cannot be used for slashing purposes.

- Currently, the endpoint can only handle "equivocation" light client attacks. This is because the "lunatic" attacks require the endpoint to possess the ability to dissociate which header is conflicted or trusted upon receiving a misbehavior message. Without this information, it's not possible to define the Byzantine validators from the conflicting headers (see [comment](https://github.com/cosmos/interchain-security/pull/826#discussion_r1268668684)).


## Consequences

### Positive
- After this ADR is applied, it will be possible for the provider chain to tombstone validators who committed a light client attack.

### Negative
- The misbehaviour verification process requires to copy a lot of unexposed IBC methods.

## References

* [ICS misbehaviour handling PR](https://github.com/cosmos/interchain-security/pull/826)
* [Architectural diagrams](https://docs.google.com/document/d/1fe1uSJl1ZIYWXoME3Yf4Aodvz7V597Ric875JH-rigM/edit#heading=h.rv4t8i6d6jfn)
