---
sidebar_position: 6
---

# Power Shaping

To give consumer chains more flexibility in choosing their validator set, Interchain Security offers
several ways to shape the powers of the validator sets on the consumer chains.

## Power Shaping Configuration

Currently, ICS supports the following power shaping parameters.

### Capping the validator set size

The consumer chain can specify a maximum number of validators it wants to have in its validator set. 
This can be used to limit the number of validators in the set, which can be useful for chains that want to have a smaller validator set for faster blocks or lower overhead. 
If more validators than the maximum size have opted in on a consumer chain, only the validators with the highest power, up to the specified
maximum, will validate the consumer chain.

Note that this parameter only applies to Opt In consumer chains (i.e., with Top N = 0).

### Capping the validator powers

The consumer chain can specify a _power cap_ which corresponds to the maximum power (percentage-wise) a validator can have on the consumer chain.
The validators-power cap is intended as a safeguard against a validator having too much power on the consumer chain and
hence "taking over" the consumer chain.
For example, if the validators-power cap is set to 32%, then no single validator can have more than 32% of the total voting
power on the consumer, and thus no single validator would be able to halt the consumer by going offline.

To respect this power cap, the voting powers of the validators that run the consumer chain are decremented or incremented
accordingly. It is important to note that the voting powers of validators on the provider do **not** change.
For example, assume that the provider chain has among others, validators `A`, `B`, `C`, and `D` with voting powers 100, 1, 1, 1 respectively.
Assume that only those 4 validators opt in on a consumer chain. Without a power cap set, validator `A`
would have 100 / (100 + 1 + 1 + 1) = ~97% of the total voting power on the consumer chain, while
validators `B`, `C`, and `D` would have 1 /(100 + 1 + 1 + 1) = ~1% of the total voting power on the consumer chain.
If the power cap is set to 30%, then the voting power of `A` would be reduced from 100 to 30 on the consumer
chain, the voting power of `B` would be increased from 1 to 25, and the power of `C` and `D` would be increased from
1 to 24. After those modifications, `A` would have 30 / (30 + 25 + 24 + 24) = ~29% of the total voting power of the
consumer chain, `B` would have 25 / (30 + 25 + 24 + 24) = ~25%, and `C` and `D` would both have 24 / (30 + 25 + 24 + 24) = ~23%.
Naturally, there are many ways to change the voting powers of validators to respect the power cap, and ICS chooses
one of them.

Note that respecting the power cap might NOT always be possible. For example, if we have a consumer
chain with only 5 validators and the power cap is set to 10%, then it is not possible to respect the
power cap. If the voting power of each validator is capped to a maximum of 10% of the total consumer
chain's voting power, then the total voting power of the consumer chain would add up to 50% which obviously does not
make sense (percentages should add up to 100%). In cases where it is not feasible to respect the power cap, all
validators on the consumer chain will have equal voting power in order to minimize the power of a single validator.
Thus, in the example of 5 validators and a power cap set to 10%, all validators would end up having 20%
of the total voting power on the consumer chain. Therefore, power-cap operates on a best-effort basis.

Note that rewards are distributed proportionally to validators with respect to their capped voting power on the consumer
and **not** their voting power on the provider.
For more information, read on [Reward Distribution](./reward-distribution.md#reward-distribution-with-power-capping).


### Allowlist and denylist

The consumer chain can specify a list of validators that are allowed or disallowed from participating in the validator set. 
If an allowlist is set, all validators not on the allowlist cannot validate the consumer chain. 
If a validator is on both lists, **_the denylist takes precedence_**, that is, they cannot validate the consumer chain.
By default, both lists are empty -- there are no restrictions on which validators are eligible to opt in.

:::warning
Note that if denylisting is used in a Top N consumer chain, then the chain might not be secured by N% of the total provider's power. 
For example, consider that the top validator `V` on the provider chain has 10% of the voting power, and we have a Top 50% consumer chain,
then if `V` is denylisted, the consumer chain would only be secured by at least 40% of the provider's power.
:::

### Minimum validator stake

The consumer chains can specify a minimum amount of stake that any validator must have on the provider chain to be eligible to opt in.
For example, setting this to 1000 would mean only validators with at least 1000 tokens staked on the provider chain can validate the consumer chain.

### Allow inactive validators

The consumer chains can specify whether validators outside of the provider's active set are eligible to opt in. 
This can be useful for chains that want to have a larger validator set than the provider chain, or for chains that want to have a more decentralized validator set.
Consumer chains that enable this feature should strongly consider setting a minimum validator stake to ensure that only validators with some reputation/stake can validate the chain.
By default, this parameter is set to `false`, i.e., validators outside of the provider's active set are not eligible to opt in. 

### Prioritylist

The consumer chain can specify a priority list of validators for participation in the validator set. Validators on the priority list are considered first when forming the consumer chain's validator set. If a priority list isn't set, the remaining slots are filled based on validator power.

## Setting Power Shaping Parameters

All the power shaping parameters can be set by the consumer chain in the `MsgCreateConsumer` or `MsgUpdateConsumer` messages.
They operate _solely on the provider chain_, meaning the consumer chain simply receives the validator set after these rules have been applied and does not have any knowledge about whether they are applied.

When setting power shaping parameters, please consider the following guidelines:

* **Do not cap the validator set size too low.** 
  Notice that this number is the **maximum** number of validators that will ever validate the consumer chain. 
  If this number is too low, the chain will be very limited in the amount of stake that secures it. 
  The validator set size cap should only be used if there are strong reasons to prefer fewer validators. 
* **Be aware of the interaction between capping the validator powers capping the validator set size.** 
  For example, if there are only 3 validators, and the cap is 20%, this will not be possible (since even splitting the power fairly would mean that each validator has 33% of the power, so is above the cap).
  Also note that the smaller this value is, the more the original voting power gets distorted, which could discourage large validators from deciding to opt in to the chain.
* **Do not have allowlist contain too few validators.** 
  If the allowlist is _non empty_, then _only_ validators on the allowlist can validate the chain.
  Thus, an allowlist containing too few validators is a security risk, e.g., the validators on the allowlist get jailed on the provider.
* **Do not have denylist contain too many validators.** 
  If the denylist is *non empty*, then the validators on the denylist cannot validate the chain.
  Thus, a denylist containing too many validators is a security risk, e.g., the validators on the denylist represents a large fraction of the provider's power. 

In general, when setting these parameters, consider that the voting power distribution in the future might be very different from the one right now,
and that the chain should be secure even if the power distribution changes significantly.

The power shaping parameters of a launched consumer chain can be changed through a [`MsgUpdateConsumer`](./permissionless.md) message.

The power shaping parameters can be seen by querying the list of consumer chains:

```bash
interchain-security-pd query provider list-consumer-chains
```

