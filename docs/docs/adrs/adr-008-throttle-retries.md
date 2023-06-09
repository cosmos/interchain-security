---
sidebar_position: 7
title: Throttle with retries
---

# ADR {008}: {Throttle with retries}

## Changelog

* {6/9/23}: Initial draft

## Status

> A decision may be "proposed" if it hasn't been agreed upon yet, or "accepted" once it is agreed upon. If a later ADR changes or reverses a decision, it may be marked as "deprecated" or "superseded" with a reference to its replacement.

Proposed

## Context

For context on why the throttling mechanism exists, see [ADR 002](./adr-002-throttle.md).

Note the terms slash throttling and jail throttling are synonymous, since in replicated security a `SlashPacket` simply jails a validator for downtime infractions.  

Currently the throttling mechanism is designed so that provider logic (slash meter, etc.) dictates how many slash packets can be handled over time. Throttled slash packets are persisted on the provider, leading to multiple possible issues. Namely:

* If slash or vsc matured packets are actually throttled/queued on the provider, state can grow and potentially lead to a DoS attack. We have short term solutions around this, but overall they come with their own weaknesses. See [#594](https://github.com/cosmos/interchain-security/issues/594).
* If a jailing attack described in [ADR 002](adr-002-throttle.md) were actually to be carried out with the current throttling design, we'd likely have to halt the provider, and perform an emergency upgrade and/or migration to clear the queues of slash packets that were deemed to be malicious. Alternatively, validators would just have to _tough it out_ and wait for the queues to clear, during which all/most validators would be jailed. Right after being jailed, vals would have to unjail themselves promptly to ensure safety. The synchronous coordination required to maintain safety in such a scenario is not ideal.

So what's the solution? We can improve the throttling mechanism to instead queue/persist relevant data on each consumer, and have consumers retry slash requests as needed.

## Decision

> This section explains all of the details of the proposed solution, including implementation details.
It should also describe affects / corollary items that may need to be changed as a part of this.
If the proposed change will be large, please also indicate a way to do the change to maximize ease of review.
(e.g. the optimal split of things to do between separate PR's)

## Consequences

> This section describes the consequences, after applying the decision. All consequences should be summarized here, not just the "positive" ones.

* Consumers will now have to manage their own queues, and retry logic.
* Consumers still aren't trustless, but the provider is now less susceptible to mismanaged or malicious consumers.
* Recovering from the "jailing attack" is more elegant.
* Some issues like [#1001](https://github.com/cosmos/interchain-security/issues/1001) will now be handled implicitly by the improved throttling mechanism.
* Slash and vsc matured packets can be handled immediately once recv by the provider if the slash meter allows.
* In general, we reduce the amount of computation that happens in the provider end-blocker.

### Positive

* We no longer have to reason about a "global queue" and a "chain specific queue", and keeping those all in-sync. Now slash and vsc matured packet queuing is handled on each consumer individually.
* Due to the above, the throttling protocol becomes less complex overall.
* We no longer have to worry about throttle related DoS attack on the provider, since no queuing exists on the provider.

### Negative

* Increased number of IBC packets being relayed anytime throttling logic is triggered.
* Consumer complexity increases, since consumers now have manage queuing themselves, and implement packet retry logic.

### Neutral

* Core throttling logic on the provider remains unchanged, ie. slash meter, replenishment cycles, etc.

## References

* [EPIC](https://github.com/cosmos/interchain-security/issues/713)
* [ADR 002](./adr-002-throttle.md)
* [#594](https://github.com/cosmos/interchain-security/issues/594)