---
sidebar_position: 7
title: Throttle with retries
---

## ADR 008: Throttle with retries

## Changelog

* 6/9/23: Initial draft

## Status

Proposed

## Context

For context on why the throttling mechanism exists, see [ADR 002](./adr-002-throttle.md).

Note the terms slash throttling and jail throttling are synonymous, since in replicated security a `SlashPacket` simply jails a validator for downtime infractions.  

Currently the throttling mechanism is designed so that provider logic (slash meter, etc.) dictates how many slash packets can be handled over time. Throttled slash packets are persisted on the provider, leading to multiple possible issues. Namely:

* If slash or vsc matured packets are actually throttled/queued on the provider, state can grow and potentially lead to a DoS attack. We have short term solutions around this, but overall they come with their own weaknesses. See [#594](https://github.com/cosmos/interchain-security/issues/594).
* If a jailing attack described in [ADR 002](adr-002-throttle.md) were actually to be carried out with the current throttling design, we'd likely have to halt the provider, and perform an emergency upgrade and/or migration to clear the queues of slash packets that were deemed to be malicious. Alternatively, validators would just have to _tough it out_ and wait for the queues to clear, during which all/most validators would be jailed. Right after being jailed, vals would have to unjail themselves promptly to ensure safety. The synchronous coordination required to maintain safety in such a scenario is not ideal.

So what's the solution? We can improve the throttling mechanism to instead queue/persist relevant data on each consumer, and have consumers retry slash requests as needed.

## Decision

### Consumer changes

Note the consumer already queues up both slash and vsc matured packets via `AppendPendingPacket`. Those packets are dequeued every endblock in `SendPackets` and sent to the provider.

Instead, we will now introduce the following logic on endblock:

* Slash packets will always be sent to the provider once they're at the head of the queue. However, once sent, the consumer will not send any trailing vsc matured packets from the queue until the provider responds with an ack that the slash packet has been handled (ie. val was jailed). That is, slash packets block the sending of trailing vsc matured packets in the consumer queue.
* If two slash packets are at the head of the queue, the consumer will send the first slash packet, and then wait for a success ack from the provider before sending the second slash packet. This seems like it'd simplify implementation.
* VSC matured packets at the head of the queue (ie. NOT trailing a slash packet) can be sent immediately, and do not block any other packets in the queue, since the provider always handles them immediately.

To prevent the provider from having to keep track of what slash packets have been rejected, the consumer will have to retry the sending of slash packets over some period of time. This can be achieved with an on-chain consumer param. The suggested param value would probably be 1/2 of the provider's `SlashMeterReplenishmentPeriod`, although it doesn't matter too much as long as the param value is sane.

Note to prevent weird edge case behavior, a retry would not be attempted until either a success ack or failure ack has been recv from the provider.

With the behavior described, we maintain very similar behavior to the current throttling mechanism regarding the timing that slash and vsc matured packets are handled on the provider. Obviously the queueing and blocking logic is moved, and the two chains would have to send more messages between one another (only in the case the throttling mechanism is triggered).

In the normal case, when no or a few slash packets are being sent, the VSCMaturedPackets will not be delayed, and hence unbonding will not be delayed.

### Provider changes

The main change needed for the provider is the removal of queuing logic for slash and vsc matured packets upon being received.

Instead, the provider will consult the slash meter to determine if a slash packet can be handled immediately. If not, the provider will return an ack message to the consumer communicating that the slash packet could not be handled, and needs to be sent again in the future (retried).

VSCMatured packets will always be handled immediately upon being received by the provider.

Note [spec](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#consumer-initiated-slashing). Specifically the section on _VSC Maturity and Slashing Order_. Previously the onus was on the provider to maintain this property via queuing packets and handling them FIFO.

Now this property will be maintained by the consumer sending packets in the correct order, and blocking the sending of VSCMatured packets as needed. Then, the ordered IBC channel will ensure that Slash/VSCMatured packets are received in the correct order on the provider.

The provider's main responsibility regarding throttling will now be to determine if a recv slash packet can be handled via slash meter etc., and appropriately ack to the sending consumer.

### Why the provider can handle VSCMatured packets immediately

First we answer, what does a VSCMatured packet communicate to the provider? A VSCMatured packet communicates that a VSC has been applied to a consumer long enough that infractions committed on the consumer could have been submitted.

If the consumer is following the queuing/blocking protocol described. No bad behavior occurs, `VSC Maturity and Slashing Order` property is maintained.

If a consumer sends VSCMatured packets too leniently: The consumer is malicious and sending duplicate vsc matured packets, or sending the packets sooner than the ccv protocol specifies. In this scenario, the provider needs to handle vsc matured packets immediately to prevent DOS, state bloat, or other issues. The only possible negative outcome is that the malicious consumer may not be able to jail a validator who should have been jailed. The malicious behavior only creates a negative outcome for the chain that is being malicious.

If a consumer blocks the sending of VSCMatured packets: The consumer is malicious and blocking vsc matured packets that should have been sent. This will block unbonding only up until the VSC timeout period has elapsed. At that time, the consumer is removed. Again the malicious behavior only creates a negative outcome for the chain that is being malicious.

### Splitting of PRs

We could split this feature into two PRs, one affecting the consumer and one affecting the provider, along with a third PR which could setup a clever way to upgrade the provider in multiple steps, ensuring that queued slash packets at upgrade time are handled properly.

## Consequences

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

* [EPIC](https://github.com/cosmos/interchain-security/issues/713) tracking the changes proposed by this ADR
* [ADR 002: Jail Throttling](./adr-002-throttle.md)
* [#594](https://github.com/cosmos/interchain-security/issues/594)