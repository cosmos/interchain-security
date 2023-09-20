---
sidebar_position: 4
title: Cryptographic verification of equivocation evidence
---
# ADR 005: Cryptographic verification of equivocation evidence

## Changelog
* 5/1/2023: First draft
* 7/23/2023: Add light client attacks handling
* 9/6/2023: Add double signing attacks handling

## Status

Accepted

## Context

Currently, we use a governance proposal to slash validators for equivocation (double signing and light client attacks). 
Every proposal needs to go through a (two weeks) voting period before it can be approved. 
Given a three-week unbonding period, this means that an equivocation proposal needs to be submitted within one week since the infraction occurred.

This ADR proposes a system to slash validators automatically for equivocation, immediately upon the provider chain's receipt of the evidence. Another thing to note is that we intend to introduce this system in stages, since even the partial ability to slash and/or tombstone is a strict improvement in security.
The feature is implemented in two parts, each with its dedicated endpoint. One endpoint handles light client attacks, while the other handles double signing attacks.

### Light Client Attack

In a nutshell, the light client is a process that solely verifies a specific state machine's
consensus without executing the transactions. The light clients get new headers by querying
multiple nodes, called primary and witness nodes. 

Light clients download new headers committed on chain from a primary. Headers can be verified in two ways: sequentially,
where the block height of headers is serial, or using skipping. This second verification method allows light clients to download headers
with nonconsecutive block height, where some intermediate headers are skipped (see [Tendermint Light Client, Figure 1 and Figure 3](https://arxiv.org/pdf/2010.07031.pdf)).
Additionally, light clients are cross-checking new headers obtained from a primary with witnesses to ensure all nodes share the same state.

A light client attack occurs when a Byzantine validator sends invalid headers to a light client.
As the light client doesn't execute transactions, it can be deceived into trusting corrupted application state transitions.
For instance, if a light client receives header `A` from the primary and header `B` from a witness for the same block height `H`,
and both headers are successfully verified, it indicates a light client attack.
Note that in this case, either the primary or the witness or both are malicious.

The types of light client attacks are defined by analyzing the differences between the conflicting headers.
There are three types of light client attacks: lunatic attack, equivocation attack, and amnesia attack. 
For details, see the [CometBFT specification](https://github.com/cometbft/cometbft/blob/main/spec/light-client/attacks/notes-on-evidence-handling.md#evidence-handling).

When a light client agent detects two conflicting headers, it will initially verify their traces (see [cometBFT detector](https://github.com/cometbft/cometbft/blob/2af25aea6cfe6ac4ddac40ceddfb8c8eee17d0e6/light/detector.go#L28)) using its primary and witness nodes.
If these headers pass successful verification, the Byzantine validators will be identified based on the header's commit signatures
and the type of light client attack. The agent will then transmit this information to its nodes using a [`LightClientAttackEvidence`](https://github.com/cometbft/cometbft/blob/feed0ddf564e113a840c4678505601256b93a8bc/docs/architecture/adr-047-handling-evidence-from-light-client.md) to be eventually voted on and added to a block.
Note that from a light client agent perspective, it is not possible to establish whether a primary or a witness node, or both, are malicious.
Therefore, it will create and send two `LightClientAttackEvidence`: one against the primary (sent to the witness), and one against the witness (sent to the primary).
Both nodes will then verify it before broadcasting it and adding it to the [evidence pool](https://github.com/cometbft/cometbft/blob/2af25aea6cfe6ac4ddac40ceddfb8c8eee17d0e6/evidence/pool.go#L28).
If a `LightClientAttackEvidence` is finally committed to a block, the chain's evidence module will execute it, resulting in the jailing and the slashing of the validators responsible for the light client attack.


Light clients are a core component of IBC. In the event of a light client attack, IBC relayers notify the affected chains by submitting an [IBC misbehavior message](https://github.com/cosmos/ibc-go/blob/2b7c969066fbcb18f90c7f5bd256439ca12535c7/proto/ibc/lightclients/tendermint/v1/tendermint.proto#L79).
A misbehavior message includes the conflicting headers that constitute a `LightClientAttackEvidence`. Upon receiving such a message,
a chain will first verify whether these headers would have convinced its light client. This verification is achieved by checking
the header states against the light client consensus states (see [IBC misbehaviour handler](https://github.com/cosmos/ibc-go/blob/2b7c969066fbcb18f90c7f5bd256439ca12535c7/modules/light-clients/07-tendermint/types/misbehaviour_handle.go#L101)). If the misbehaviour is successfully verified, the chain will then "freeze" the
light client, halting any further trust in or updating of its states.


## Decision

In the first part of the feature, we will introduce a new endpoint: `HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour)`.
The main idea is to leverage the current IBC misbehaviour handling and update it to solely jail and slash the validators that
performed a light client attack. This update will be made under the assumption that the chain connected via this light client
share the same validator set, as it is the case with Replicated Security. 

This endpoint will reuse the IBC client libraries to verify that the misbehaviour headers would have fooled the light client.
Additionally, it’s crucial that the endpoint logic result in the slashing and jailing of validators under the same conditions
as a light client agent detector. Therefore, the endpoint will ensure that the two conditions are met:
the headers in the misbehaviour message have the same block height, and
the light client isn’t expired.

After having successfully verified a misbehaviour, the endpoint will execute the jailing and slashing of the malicious validators similarly as in the evidence module. 


### Double Signing Attack

A double signing attack, also known as equivocation, 
occurs when a validator votes for two different blocks in the same round of the CometBFT consensus. 
This consensus mechanism operates with multiple voting rounds at each block height, 
and it strictly prohibits sending two votes of the same type during a round 
(see [CometBFT State Machine Overview](https://github.com/cometbft/cometbft/blob/2af25aea6cfe6ac4ddac40ceddfb8c8eee17d0e6/spec/consensus/consensus.md#state-machine-overview)).

When a node observes two votes from the same peer, it will use these two votes to create 
a [`DuplicateVoteEvidence`](https://github.com/cometbft/cometbft/blob/v0.34.28/types/evidence.go#L35) 
evidence and gossip it to the other nodes in the network 
(see [CometBFT equivocation detection](https://github.com/cometbft/cometbft/blob/2af25aea6cfe6ac4ddac40ceddfb8c8eee17d0e6/spec/consensus/evidence.md#detection)). 
Each node will then verify the evidence according to the CometBFT rules that define a valid double signing infraction, and based on this verification, they will decide whether to add the evidence to a block. 
During the evidence verification process, the signatures of the conflicting votes must be verified successfully. 
Note that this is achieved using the public key of the misbehaving validator, along with the chain ID of the chain where the infraction occurred (see [CometBFT equivocation verification](https://github.com/cometbft/cometbft/blob/2af25aea6cfe6ac4ddac40ceddfb8c8eee17d0e6/spec/consensus/evidence.md#verification)).

Once a double signing evidence is committed to a block, the consensus layer will report the equivocation to the evidence module of the Cosmos SDK application layer. 
The application will, in turn, punish the malicious validator through jailing, tombstoning and slashing 
(see [handleEquivocationEvidence](https://github.com/cosmos/cosmos-sdk/blob/19389505643500b25a5efeb02715c3deef9b6ede/x/evidence/keeper/infraction.go#L27C17-L27C43)).

## Decision

In the second part of the feature, we will introduce a new endpoint `HandleConsumerDoubleVoting(
ctx sdk.Context, evidence *tmtypes.DuplicateVoteEvidence, chainID string, pubkey cryptotypes.PubKey)`. 
Simply put, the handling logic will verify a double signing evidence against a provided 
public key and chain ID and, if successful, execute the jailing of the malicious validator who double voted.
  
We will define a new 
[`MsgSubmitConsumerDoubleVoting`](https://github.com/cosmos/interchain-security/blob/20b0e35a6d45111bd7bfeb6845417ba752c67c60/proto/interchain_security/ccv/provider/v1/tx.proto#L69C9-L69C38) 
message to report a double voting evidence observed 
on a consumer chain to the endpoint of the provider chain. This message will contain two fields: 
a double signing evidence 
[`duplicate_vote_evidence`](https://github.com/cosmos/interchain-security/blob/20b0e35a6d45111bd7bfeb6845417ba752c67c60/proto/interchain_security/ccv/provider/v1/tx.proto#L75) 
and a light client header for the infraction block height, 
referred to as [`infraction_block_header`](https://github.com/cosmos/interchain-security/blob/20b0e35a6d45111bd7bfeb6845417ba752c67c60/proto/interchain_security/ccv/provider/v1/tx.proto#L77). 
The latter will provide the malicious validator's public key and the chain ID required to verify the signature of the votes contained in the evidence.
 
Note that double signing evidence will be verified by using the same conditions than in the CometBFT 
[`verify(evidence types.Evidence)`](https://github.com/cometbft/cometbft/blob/2af25aea6cfe6ac4ddac40ceddfb8c8eee17d0e6/evidence/verify.go#L19) 
method, with the exception that its age won't be checked. 
This is primarily because, for the first stage of this feature, 
the goal is to jail validators for double signing only. Since the jail time doesn't depend on the evidence's age, 
it can be ignored. More technical details can be found in the ["Current limitations"](#current-limitations) section below. 
  
  
Upon a successful equivocation verification, the misbehaving validator will be jailed for the maximum time 
(see [DoubleSignJailEndTime](https://github.com/cosmos/cosmos-sdk/blob/cd272d525ae2cf244c53433b6eb1e835783d7531/x/evidence/types/params.go) 
in the SDK evidence module).


### Current limitations:

- We cannot derive an infraction height from the evidence, so it is only possible to jail validators, not actually slash them.
To explain the technical reasons behind this limitation, let's recap the initial consumer initiated slashing logic.
 In a nutshell, consumer heights are mapped to provider heights through VSCPackets, namely through the so called vscIDs.
 When an infraction occurs on the consumer, a SlashPacket containing the vscID obtained from mapping the consumer infraction height
 is sent to the provider. Upon receiving the packet, the provider maps the consumer infraction height to a local infraction height,
 which is used to slash the misbehaving validator. In the context of untrusted consumer chains, all their states, including vscIDs,
 could be corrupted and therefore cannot be used for slashing purposes.

- For the same reasons explained above, the age of a consumer double signing evidence can't be verified, 
either using its infraction height or its unsigned timestamp.

- In the first stage of this feature, validators are jailed indefinitely without being tombstoned.
The underlying reason is that a malicious validator could take advantage of getting tombstoned 
to avoid being slashed on the provider ([see comment](https://github.com/cosmos/interchain-security/pull/1232#issuecomment-1693127641)). 

- Currently, the endpoint can only handle "equivocation" light client attacks. This is because the "lunatic" attacks require the endpoint to possess the ability to dissociate which header is conflicted or trusted upon receiving a misbehavior message. Without this information, it's not possible to define the Byzantine validators from the conflicting headers (see [comment](https://github.com/cosmos/interchain-security/pull/826#discussion_r1268668684)).


## Consequences

### Positive

- After this ADR is applied, it will be possible for the provider chain to jail validators who committed 
light client or double signing attacks.

### Negative

- N/A


## References

* [ICS misbehaviour handling PR](https://github.com/cosmos/interchain-security/pull/826)
* [Consumer double voting handler PR](https://github.com/cosmos/interchain-security/pull/1232)
* [Architectural diagrams](https://docs.google.com/document/d/1fe1uSJl1ZIYWXoME3Yf4Aodvz7V597Ric875JH-rigM/edit#heading=h.rv4t8i6d6jfn)
* [ADR on equivocation slashing](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-013-equivocation-slashing.md)
