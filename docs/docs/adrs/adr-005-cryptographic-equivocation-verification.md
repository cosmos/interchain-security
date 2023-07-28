---
sidebar_position: 4
title: Cryptographic verification of equivocation evidence
---
# ADR 005: Cryptographic verification of equivocation evidence

## Changelog
* 5/1/2023: First draft
* 7/23/23: Add light attack handling

## Status

Proposed

## Context

Currently, we use a governance proposal to slash validators for equivocation (double signing and light client attacks). This has the downside that it takes 2 weeks for the proposal to be approved, effectively reducing the unbonding period in some respects. This does not lead to any pressing real-world security concerns, but since it involves the basis of proof of stake, it would be good to get consumer chain slashing back to parity as soon as possible.

This ADR proposes a system to slash validators automatically for equivocation, immediately upon the provider chain's receipt of the evidence. Another thing to note is that we intend to introduce this system in stages, since even the partial ability to slash and/or tombstone is a strict improvement in security.
For the first stage of this work, we will only handle light client attacks(LCA).

### Ligth Client Attack

In a nutshell, the light client is a process that solely verifies a specific state machine's
consensus without executing the transactions. The light clients get new headers by querying
multiple nodes, called primary and witness nodes. 

Headers can be verified in two ways: sequentially, where verification occurs in order of block height,
and each new header must be signed by ⅔+ of the voting power from the last trusted header validators;
or using skipping, where intermediate headers are verified and must be signed by ⅓+ of the voting power
from the last trusted header validators (TODO: add ref). The latter is the default method, as it is faster in most cases.
Additionally, light clients are cross-checking new headers obtained from the primary with witnesses to ensure all nodes share the same states.

A light client attack occurs when Byzantine validators send incorrect states to a light client.
As the light client doesn't execute transactions, it can be deceived into trusting corrupted application states.
For instance, if the light client receives header A from the primary and header B from the witness, both successfully verified,
for the same block height, it indicates a light client attack.

In this case, there are two possible scenarios: either the primary and/or witness nodes are malicious,
what it’s called a “light fork”; or there is a standard fork happening on the chain.

To orchestrate a light fork, byzantine actors create a header with incorrect states that must be signed by ⅓+ of the voting power.
The types of light client attacks are defined by analyzing the differences between the conflicting headers.
If some deterministic states aren’t equal, i.e. states resulting from a previous block
(see [block header def.](https://github.com/cometbft/cometbft/blob/2af25aea6cfe6ac4ddac40ceddfb8c8eee17d0e6/types/block.go#L325)),
like `NextValidatorHash` or `AppHash`, is called a “lunatic attack”, in the opposite case an “equivocation”.

When a light client agent detects two conflicting headers, it will initially verify their traces (see [cometBFT detector](https://github.com/cometbft/cometbft/blob/2af25aea6cfe6ac4ddac40ceddfb8c8eee17d0e6/light/detector.go#L28)) using its primary and witness nodes.
If these headers pass successful verification, the Byzantine validators will be identified based on the header's commit signatures
and the type of light client attack. The agent will then transmit this information to its node using a `LightClientAttackEvidence` (TODO: add comet ref.) to be eventually voted and commited it to a block. In this scenario, the chain's evidence module (TODO: add ev. ref) will execute the jailing and the slashing of the validators responsible for the light client attack.

In the event of an attack against one of its light clients, the counter-party chains implement necessary measures.
The IBC relayers facilitate a way to notify these chains of a detected light client attack by submitting an [IBC misbehavior message]((https://github.com/cosmos/ibc-go/blob/2b7c969066fbcb18f90c7f5bd256439ca12535c7/proto/ibc/lightclients/tendermint/v1/tendermint.proto#L79)).
A misbehavior message includes the conflicting headers that constitute a `LightClientAttackEvidence`. Upon receiving such a message,
a chain will first verify whether these headers would have convinced its light client. This verification is achieved by checking
the header states against the light client consensus states (see [IBC misbehaviour handler](https://github.com/cosmos/ibc-go/blob/2b7c969066fbcb18f90c7f5bd256439ca12535c7/modules/light-clients/07-tendermint/types/misbehaviour_handle.go#L101)). If the misbehavior is successfully verified, the chain will then "freeze" the
light client, halting any further trust in or updating of its states.


## Decision

In the first iteration of the feature, we will introduce a new endpoint: `HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour)`.
The main idea is to leverage the current IBC misbehavior handling and update it to solely jail and slash the validators that
performed a light client attack. This update will be made under the assumption that the chains connected via this light client
share the same validator set, as in the ICS context.

This endpoint will reuse the IBC client libraries to verify that the misbehaviour headers would have fool the light client.
Addionally, it’s crucial that the endpoint logic result in the slashing and jailing of validators under the same conditions
as a light client agent detector. Therefore, the endpoint will ensure that the two conditions are met:
the misbehaviour’s header contains the same block height, and
the light client isn’t expired.

After having successfully verified a misbeheaviour, the endpoint will execute the jailing and slashing of the malicious validators similarly as in the evidence module. 

### Current limitations:

- This only handles light client attacks, not double signing. In the future, we will add the code to also verify double signing.

- We cannot derive an infraction height from the evidence, so it is only possible to tombstone validators, not actually slash them.
To explain the technical reasons behind this limitation, let's recap the initial consumer initiated slashing logic.
In a nutshell, consumer heights are mapped to provider heights through VSCPackets, namely through the so called vscIDs.
When an infraction occurs on the consumer, a SlashPacket containing the vscID obtained from mapping the consumer infraction height
is sent to the provider. Upon receiving the packet, the provider maps the consumer infraction height to a local infraction height,
which is used to slash the misbehaving validator. In the context of untrusted consumer chains, all their states, including vscIDs,
could be corrupted and the ore cannot be used for slashing purposes.

- The endpoint can only handle "equivocation" light client attacks at the moment. The issue with the "lunatic" attack is that it's impossible for the endpoint to distinguish which header is conflicted or trusted when receiving a misbehaviour message (see [comment](https://github.com/cosmos/interchain-security/pull/826#discussion_r1268668684)).


## Consequences

After this ADR is applied, it will be possible for the provider chain to tombstone validators who committed a light client attack.

## References

* [ICS misbehaviour handling PR](https://github.com/cosmos/interchain-security/pull/826/files)
* [Architecture plan](https://docs.google.com/document/d/1fe1uSJl1ZIYWXoME3Yf4Aodvz7V597Ric875JH-rigM/edit#heading=h.rv4t8i6d6jfn)
