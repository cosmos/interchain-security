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
- `consumer-pub-key` is an **optional** field that corresponds to the public key the validator wants to use on the
consumer chain, and it has the following format `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"<key>"}`.

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
By setting the `consumer-pub-key`, a validator can both opt in to a chain, as well as, assign a
public key on a consumer chain. Note that a validator can always issue a [key assignment](../features/key-assignment.md)
at a later stage to assign a new consumer public key on a chain. The key-assignment [rules](../features/key-assignment.md#rules)
still apply when setting `consumer-pub-key` when opting in.
:::

:::info
A validator is only eligible for consumer rewards from a consumer chain if the validator is opted in on that chain.
:::

### How to opt out from a consumer chain?
A validator can opt out from a consumer by issuing the following message:

```bash
interchain-security-pd tx provider opt-out <consumer-chain-id>
```
where
- `consumer-chain-id` is the string identifier of the consumer chain.

:::warning
A validator cannot opt out from a Top N chain if it belongs to the top N% validators on that chain.
:::

:::warning
A validator can stop its node on a consumer chain **only** after opting out and confirming through the `has-to-validate`
query (see [below](./partial-set-security-for-validators.md#which-chains-does-a-validator-have-to-validate)) that it does
not have to validate the consumer chain any longer.
:::

:::warning
If all validators opt out from an Opt-In chain, then the chain would halt.
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
If a validator is automatically opted in to a Top N chain, then this is reflected in the results of the query.


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