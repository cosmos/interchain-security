---
sidebar_position: 6
---

# Partial Set Security

[Partial Set Security](../features/partial-set-security.md) allows consumer chains to join as Opt-In or Top N.
Here, we show how a validator can opt in, opt out, or set a custom commission rate on a consumer chain, as well
as useful queries that a validator can use to figure out which chains it has to validate, etc.

## Messages
### How to opt in to a consumer chain?

:::warning
A validator is automatically opted in to a Top N chain if the validator belongs to the top N% of the validators on the provider chain.
:::

In a Top N chain, a validator that does not belong to the top N% of the validators on the provider can still choose
to opt in to a consumer chain. In other words, validators can opt in, in both Opt-In and Top N chains.

A validator can opt in to a consumer chain by issuing the following message:
```bash
interchain-security-pd tx provider opt-in <consumer-chain-id> <optional consumer-pub-key>
```

where
- `consumer-chain-id` is the string identifier of the consumer chain the validator wants to opt in to;
- `consumer-pub-key` corresponds to the public key the validator wants to use on the consumer chain, and it has the
following format `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"<key>"}`.

A validator can opt in to an existing consumer chain that is already running, or to a [proposed](../features/proposals.md)
consumer chain that is still being voted on. A validator can use the following command to retrieve the currently existing
consumer chains:
```bash
interchain-security-pd query provider list-consumer-chains
```
and this command to see the currently proposed consumer chains:
```bash
interchain-security-pd query provider list-proposed-consumer-chains
```


:::tip
By setting the `consumer-pub-key`, a validator can both opt in to a chain and assign a
public key on a consumer chain. Note that a validator can always [assign](../features/key-assignment.md)
a new consumer key at a later stage. The key-assignment [rules](../features/key-assignment.md#rules)
still apply when setting `consumer-pub-key` when opting in.
:::

:::info
A validator is only eligible for consumer rewards from a consumer chain if the validator is opted into that chain.
:::

### How to opt out from a consumer chain?
A validator can opt out from a consumer by issuing the following message:

```bash
interchain-security-pd tx provider opt-out <consumer-chain-id>
```
where
- `consumer-chain-id` is the string identifier of the consumer chain.

:::warning
A validator cannot opt out from a Top N chain if it belongs to the top N% validators of the provider.
:::

:::warning
If a validator moves from the Top N to outside of the top N% of the validators on the provider, it will **not**
be automatically opted-out. The validator has to manually opt out.
:::

:::warning
A validator can stop its node on a consumer chain **only** after opting out and confirming through the `has-to-validate`
query (see [below](./partial-set-security-for-validators.md#which-chains-does-a-validator-have-to-validate)) that it does
not have to validate the consumer chain any longer.
:::

:::warning
If all validators opt out from an Opt-In chain, the chain will halt with a consensus failure upon receiving the VSCPacket with an empty validator set.
:::

### How to set specific per consumer chain commission rate?
A validator can choose to set a different commission rate on each of the consumer chains it validates.
This can be done with the following command:
```bash
interchain-security-pd tx provider set-consumer-commission-rate <consumer-chain-id> <commission-rate>
```
where

- `consumer-chain-id` is the string identifier of the consumer chain;
- `comission-rate` decimal in `[minRate, 1]` where `minRate` corresponds to the minimum commission rate set on the
provider chain (see `min_commission_rate` in `interchain-security-pd query staking params`).

'''tip
If a validator does not set a commission rate on a consumer chain, the commission rate defaults to their commission rate on the provider chain.
'''


## Queries
Partial Set Security introduces a number of queries to assist validators determine which consumer chains they have to
validate, their commission rate per chain, etc.

### Which chains does a validator have to validate?
Naturally, a validator is aware of the Opt-In chains it has to validate because in order to validate an Opt-In chain,
a validator has to manually opt in to the chain. This is not the case for Top N chains where a validator might be required
to validate such a chain without explicitly opting in if it belongs to the top N% of the validators on the provider.

We introduce the following query:
```bash
interchain-security-pd query provider has-to-validate <provider-validator-address>
```
that can be used by validator with `provider-validator-address` address to retrieve the list of chains that it has to validate.


:::tip
As a validator, the list of chains returned by `has-to-validate` is the list of chains you **should** be validating to avoid
getting jailed for downtime.
:::

### How do you know how much voting power you need to have to be in the top N for a chain?
This can be seen as part of the `list-consumer-chains` query:
```bash
interchain-security-pd query provider list-consumer-chains
```
where the `min_power_in_top_N` field shows the minimum voting power required to be
automatically opted in to the chain.

:::tip
`list-consumer-chains` shows the minimal voting power *right now*, but
the automatic opt-in happens only when epochs end on the provider.
In consequence, a validators power might be large enough to be automatically opted in
during an epoch, but if their power is sufficiently decreased before the epoch ends,
they will not be opted in automatically.
:::


### How to get all the opted-in validators on a consumer chain?
With the following query:
```bash
interchain-security-pd query provider consumer-opted-in-validators <consumer-chain-id>
```
we can see all the opted-in validators on `consumer-chain-id` that were manually or automatically opted in.

### How can we see the commission rate a validator has set on a consumer chain?
Using the following query:
```bash
interchain-security-pd query provider validator-consumer-commission-rate <consumer-chain-id> <provider-validator-address>
```
we retrieve the commission rate set by validator with `provider-validator-address` address on `consumer-chain-id`.