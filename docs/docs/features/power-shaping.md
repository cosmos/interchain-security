# Power Shaping

To give consumer chains more flexibility in choosing their validator set, Interchain Security v2
introduces several "power shaping" mechanisms.

These are:
1) **Capping the size of the validator set**: The consumer chain can specify a maximum number of validators it
wants to have in its validator set. This can be used to limit the number of validators in the set, which can
be useful for chains that want to have a smaller validator set for faster blocks or lower overhead.
*Note*: This is only applicable to Opt In chains (chains with Top N = 0).
1) **Capping the fraction of power any single validator can have**: The consumer chain can specify a maximum fraction
of the total voting power that any single validator in its validator set should have.
This is a security measure with the intention of making it harder for a single large validator to take over a consumer chain. This mitigates the risk of an Opt In chain with only a few validators being dominated by a validator with a large amount of voting power opting in.
For example, setting this fraction to e.g. 33% would mean that no single validator can have more than 33% of the total voting power,
and thus there is no single validator who would stop the chain by going offline.
Note that this is a soft cap, and the actual power of a validator can exceed this fraction if the validator set is small (e.g. there are only 3 validators and the cap is 20%).
1) **Allowlist and denylist**: The consumer chain can specify a list of validators that are allowed or disallowed from participating in the validator set. If an allowlist is set, all validators not on the allowlist cannot validate the consumer chain. If a validator is on both lists, the denylist takes precedence, that is, they cannot validate the consumer chain. If neither list is set, all validators are able to validate the consumer chain.

All these mechanisms are set by the consumer chain in the `ConsumerAdditionProposal`. They operate *solely on the provider chain*, meaning the consumer chain simply receives the validator set after these rules have been applied and does not have any knowledge about whether they are applied.

Each of these mechanisms is *set during the consumer addition proposal* (see [Onboarding](../consumer-development/onboarding.md#3-submit-a-governance-proposal)), and is currently *immutable* after the chain has been added.
