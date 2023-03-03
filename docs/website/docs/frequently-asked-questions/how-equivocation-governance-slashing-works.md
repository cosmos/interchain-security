---
sidebar_position: 13
---

# How Equivocation Governance Slashing works?

To avoid potential attacks directed at provider chain validators, a new mechanism was introduced:

When a validator double-signs on the provider chain a special type of slash packet is relayed to the provider chain. The provider will store information about the double signing validator and allow a governance proposal to be submitted.
If the double-signing proposal passes, the offending validator will be slashed on the provider chain and tombstoned. Tombstoning will permanently exclude the validator from the active set of the provider.

An equivocation proposal cannot be submitted for a validator that did not double sign on any of the consumer chains.

