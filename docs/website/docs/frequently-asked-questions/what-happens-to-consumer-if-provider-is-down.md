---
sidebar_position: 3
---

# What happens to consumer if provider is down?

In case the provider chain halts or experiences difficulties the consumer chain will keep operating - the provider chain and consumer chains represent different networks, which only share the validator set.

The consumer chain will not halt if the provider halts because they represent distinct networks and distinct infrastructures. Provider chain liveness does not impact consumer chain liveness.

However, if the `trusting_period` (currently 5 days for protocol safety reasons) elapses without receiving any updates from the provider, the consumer chain will essentially transition to a Proof of Authority chain.
This means that the validator set on the consumer will be the last validator set of the provider that the consumer knows about.

Steps to recover from this scenario and steps to "release" the validators from their duties will be specified at a later point.
At the very least, the consumer chain could replace the validator set, remove the ICS module and perform a genesis restart. The impact of this on the IBC clients and connections is currently under careful consideration.

