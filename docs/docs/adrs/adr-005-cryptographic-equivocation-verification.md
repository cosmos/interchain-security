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
- We currently can't derive an infraction height from the evidence, so it is only possible to tombstone validators, not actually slash them. To explain the technical reasons behind this limitation, let's recap the initial consumer initiated slashing logic. In the previous implementation, Validator Set Update IDs (VSCIDs) were used to derive the infraction height from evidences. Each VSCID was mapped to a block height and stored on both the provider and consumer chains. When an infraction occurred on a consumer chain, a IBC slashing packet was sent to the provider chain along with a VSCID obtained from mapping the evidence's infraction height. Upon receiving the packet, the provider could derive its own local infraction height to execute the slashing. In the context of untrusted consumer chains, all their states, including VSCIDs, could be corrupted and therefore cannot be used for slashing purposes. To address this, we explored a solution using the IBC misbehavior type, which includes the validator set active during the light client attack.By mapping each validator set hash to a block height, the provider would be able to derive an infraction height from an evidence again. However, this solution fails to consider that non-consecutive blocks can have the exact same validator set. In this scenario the validator set hashes would be identical for different unique block height making the mapping obsolete.


## Consequences

After this ADR is applied, it will be possible for the provider chain to tombstone validators who committed a light client attack.

## References

* [{reference link}](https://github.com/cosmos/interchain-security/pull/826/files)
