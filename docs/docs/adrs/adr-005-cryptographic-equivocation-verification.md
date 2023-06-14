---
sidebar_position: 4
title: Cryptographic verification of equivocation evidence
---
# ADR 005: Cryptographic verification of equivocation evidence

## Changelog
* 5/1/2023: First draft

## Status

Proposed

## Context

Currently, we use a governance proposal to slash validators for equivocation (double signing and light client attacks). This has the downside that it takes 2 weeks for the proposal to be approved, effectively reducing the unbonding period in some respects. This does not lead to any pressing real-world security concerns, but since it involves the basis of proof of stake, it would be good to get consumer chain slashing back to parity as soon as possible.

This ADR proposes a system to slash validators automatically for equivocation, immediately upon the provider chain's receipt of the evidence. Another thing to note is that we intend to introduce this system in stages, since even the partial ability to slash and/or tombstone is a strict improvement in security.

## Decision

For the first stage of this work, we will only handle light client attacks, since there is already code available in the IBC libraries to handle them. We will introduce a new endpoint- `HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour)`. This endpoint takes evidence of a light client attack of the type used by IBC. It then uses various methods from IBC to cryptographically verify the evidence. It then tombstones validators based on this evidence.

Current limitations:

- This only handles light client attacks, not double signing. In the future, we will add the code to also verify double signing.
- Since a special endpoint must be used to submit the evidence, the evidence is not automatically submitted by Hermes. In the future, we may make Hermes submit the evidence, or use a hook provided by IBC to run the code automatically when evidence is submitted to the IBC client. In the current state, someone will need to submit the evidence manually in the 3 weeks after a light client attack has occured.
- We currently can't derive an infraction height from the evidence, so it is only possible to tombstone validators, not actually slash them. 
In order to introduce the technical reasons of this limitation let's recall the fondation of the CCV slashing feature (now disabled under the untrusted consumer chain) to translate an infraction height from consumer to provider.

From the CCV protocol foundation each validator set -updates? active on a provider chain will be reflected on its consumer chains.
When an attack occured on a consumer chain its current active validator set should be slashed on the provider chain.
On the provider, each validator set get asssigned an VSCID which is then mapped to a block height and stored.
This mapping allows to translate between provider and consumer under which validator set an event(unbonding/slashing) occured. 

Under the untrusted consumer chain narrative, ICS misbehaviour handling is sued over the VSCID sent from a consumer chain can be fraudulent and can't be used to slashing tokens.
Therefore 


An attack that occured on a consumer chain securized under a validator set with ID vscid1 must be reported 


 let's recall that the infraction height is required by the slashing mechanism in order take in account the unbonding delegations
which occured after the infraction height on the consumer. The first naive approach is to use the valset available on the IBC misbehaviour header. This valset
can be mapped through a VSC ID and then map to a block height on the provider. However, a limitation stem to the fact that validator set are not unique and may be the same along different block height.
This solution can end up in a situation where V at VSCID1 determine the infraction height but a prior valset V' within the unbonding period would be slashed and the so the undelegations unfairly.



    - What is needed to slash according to consumer initiated slashing
        - why we need it unbondings
        - VSCID mapping
            - give spec link

    - Introduce IBC Misbehaviour data
        -   Valset, TS ...

    - 1st approach naive approach using valset
        - valset hash -> VSCID mapping - why we thought it was easy
        - how to do it
        - limitations n how it can be aribitraly broken or played

    - 2nd approach using timestamp
        - tought experiemnt
        - result in most basic attack 
        - limitations n how it can be aribitraly broken or played
    
    Conlclusion
        potential directions








## Consequences

After this ADR is applied, it will be possible for the provider chain to tombstone validators who committed a light client attack.

## References

* [{reference link}](https://github.com/cosmos/interchain-security/pull/826/files)
