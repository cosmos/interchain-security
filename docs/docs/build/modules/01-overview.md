---
sidebar_position: 1
---

# Overview

ICS consists of two main modules:

* [x/provider](./02-provider.md)
  * Provides to consumer chains updated information of opted in validators.
  * Distributes ICS rewards to opted in validators.
  * Jails and slashes validators that misbehave on consumer chains.  
* [x/consumer](./03-consumer.md)
  * Sends to the consensus engine the validator sets received from the provider chain.
  * Splits consumer block rewards and sends ICS rewards to the provider chain. 
  * Notifies the provider chain of downtime infractions. 

Note that `x/types` contains types shared by both modules.

In addition, the following modules are added to ICS to extend its functionality:

* [x/democracy](04-democracy.md)