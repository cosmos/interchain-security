# Power Shaping

To give consumer chains more flexibility in choosing their validator set, Interchain Security offers
several "power shaping" mechanisms for consumer chains.

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

:::warning
Note that if denylisting is used in a Top N consumer chain, then the chain might not be secured by N% of the total provider's
power. For example, consider that the top validator `V` on the provider chain has 10% of the voting power, and we have a Top 50% consumer chain,
then if `V` is denylisted, the consumer chain would only be secured by at least 40% of the provider's power.
:::

All these mechanisms are set by the consumer chain in the `ConsumerAdditionProposal`. They operate *solely on the provider chain*, meaning the consumer chain simply receives the validator set after these rules have been applied and does not have any knowledge about whether they are applied.

Each of these mechanisms is *set during the consumer addition proposal* (see [Onboarding](../consumer-development/onboarding.md#3-submit-a-governance-proposal)), and is currently *immutable* after the chain has been added.

The values can be seen by querying the list of consumer chains:
```bash
interchain-security-pd query provider list-consumer-chains
```

## Guidelines for setting power shaping parameters

When setting power shaping parameters, please consider the following guidelines:
* Do not cap the validator set size too low: Notice that this number is the **maximum* number of validators that will ever validate the consumer chain. If this number is too low, the chain will be very limited in the
amount of stake that secures it. The validator set size cap should only be used if there are strong reasons to prefer fewer validators. Consider that setting the cap will mean that
even if the whole validator set of the provider wants to validate on the chain, some validators will simply not be able to.
* Capping the fraction of power any single validator can have is a decent security measure, but it's good to be aware of the interactions with the size of the validator set.
For example, if there are only 3 validators, and the cap is 20%, this will not be possible (since even splitting the power fairly would mean that each validator has 33% of the power, so is above the cap).
However, the cap can be a good measure to prevent a single large validator from essentially taking over the chain.
In general, values under 33% make sense (since a validator that has 33% of the chains power would halt the chain if they go offline).
Notice that the smaller this value is, the more the original voting power gets distorted, which could discourage large validators from deciding to opt in to the chain.
* If the allowlist is *empty*, all validators can validate the chain. If it is *non empty*, then *only* validators on the allowlist can validate the chain.
Thus, an allowlist containing too few validators is a security risk. In particular, consider that if the validators on the allowlist lose a lot of stake or stop being validators,
an allowlist that is too short can very quickly become outdated and leave too few validators, or validators with too little stake, to secure the chain in a decentralized way.
* If the denylist is too full, this can likewise be problematic. If too many large validators are denylisted, the chain might not be secured by a large enough fraction of the provider's power, in particular when
the power distribution on the provider shifts and the denylisted validators gain more power.

In general, when setting these parameters, consider that the voting power distribution in the future might be very different from the one right now,
and that the chain should be secure even if the power distribution changes significantly.