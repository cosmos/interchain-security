---
sidebar_position: 4
title: Equivocation governance proposal
---
# ADR 003: Equivocation governance proposal

## Changelog
* 2023-02-06: Initial draft
* 2023-11-30: Change status to deprecated

## Status

Deprecated

## Context

**Note:** ADR deprecated as the equivocation proposal was removed by the 
cryptographic verification of equivocation feature 
(see [ADR-005](./adr-005-cryptographic-equivocation-verification.md) and 
[ADR-013](./adr-013-equivocation-slashing.md)).

We want to limit the possibilities of a consumer chain to execute actions on the provider chain to maintain and ensure optimum security of the provider chain.

For instance, a malicious consumer consumer chain can send slash packet to the provider chain, which will slash a validator without the need of providing an evidence.

## Decision

To protect against a malicious consumer chain, slash packets unrelated to downtime are ignored by the provider chain. Thus, an other mechanism is required to punish validators that have committed a double-sign on a consumer chain.

A new kind of governance proposal is added to the `provider` module, allowing to slash and tombstone a validator for double-signing in case of any harmful action on the consumer chain.

If such proposal passes, the proposal handler delegates to the `evidence` module to process the equivocation. This module ensures the evidence isn’t too old, or else ignores it (see [code](https://github.com/cosmos/cosmos-sdk/blob/21021b837882d1d40f1d79bcbc4fad2e79a3fefe/x/evidence/keeper/infraction.go#L54-L62)). *Too old* is determined by 2 consensus params : 

- `evidence.max_age_duration` number of nanoseconds before an evidence is considered too old
- `evidence.max_age_numblocks` number of blocks before an evidence is considered too old.

On the hub, those parameters are equals to 

```json
// From https://cosmos-rpc.polkachu.com/consensus_params?height=13909682
(...)
"evidence": {
	"max_age_num_blocks": "1000000",
	"max_age_duration": "172800000000000",
  (...)
},
(...)
```

A governance proposal takes 14 days, so those parameters must be big enough so the evidence provided in the proposal is not ignored by the `evidence` module when the proposal passes and is handled by the hub.

For `max_age_num_blocks=1M`, the parameter is big enough if we consider the hub produces 12k blocks per day (`blocks_per_year/365 = 436,0000/365`). The evidence can be up to 83 days old (`1,000,000/12,000`) and not be ignored.

For `max_age_duration=172,800,000,000,000`, the parameter is too low, because the value is in nanoseconds so it’s 2 days. Fortunately the condition that checks those 2 parameters uses a **AND**, so if `max_age_num_blocks` condition passes, the evidence won’t be ignored.

## Consequences

### Positive

* Remove the possibility from a malicious consumer chain to “attack” the provider chain by slashing/jailing validators.
* Provide a more acceptable implementation for the validator community.

### Negative

* Punishment action of double-signing isn’t “automated”, a governance proposal is required which takes more time.
* You need to pay 250ATOM to submit an equivocation evidence.

### Neutral

## References

* PR that ignores non downtime slash packet : [https://github.com/cosmos/interchain-security/pull/692](https://github.com/cosmos/interchain-security/pull/692)
* PR that adds the governance slash proposal: [https://github.com/cosmos/interchain-security/pull/703](https://github.com/cosmos/interchain-security/pull/703)
