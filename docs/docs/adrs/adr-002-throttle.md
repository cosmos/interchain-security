---
sidebar_position: 3
title: Jail Throttling
---

# ADR 002: Jail Throttling

## Changelog

* 2023-01-26: Initial Draft
* 2023-02-07: Property refined, ADR ready to review/merge

## Status

Accepted

## Context

The CCV spec is based around the assumption that the provider binary and all consumers binaries are non-malicious, and follow the defined protocols. In practice, this assumption may not hold. A malicious consumer binary could potentially include code which is able to send many slash/jail packets at once to the provider.

Before the throttling feature was implemented, the following attack was possible. Attacker(s) would create provider validators just below the provider's active set. Using a malicious consumer binary, slash packets would be relayed to the provider, that would slash/jail a significant portion (or all) of honest validator at once. Control of the provider would then pass over to the attackers' validators. This enables the attacker(s) to halt the provider. Or even worse, commit arbitrary state on the provider, potentially stealing all tokens bridged to the provider over IBC.

## Decision

The throttling feature was designed to slow down the mentioned attack from above, allowing validators and the community to appropriately respond to the attack. Ie. this feature limits (enforced by on-chain params) the rate that the provider validator set can be jailed over time.

### State Required - Slash Meter

There exists one slash meter on the provider which stores an amount of voting power (integer), corresponding to an allowance of validators that can be jailed over time. This meter is initialized to a certain value on genesis, decremented by the amount of voting power jailed whenever a slash packet is handled, and periodically replenished as decided by on-chain params.

### State Required - Global entry queue

There exists a single queue which stores "global slash entries". These entries allow the provider to appropriately handle slash packets sent from any consumer in FIFO ordering. This queue is responsible for coordinating the order that slash packets (from multiple chains) are handled over time.

### State Required - Per-chain data queue

For each established consumer, there exists a queue which stores "throttled packet data". Ie. pending slash packet data is queued together with pending VSC matured packet data in FIFO ordering. Order is enforced by IBC sequence number. These "per-chain" queues are responsible for coordinating the order that slash packets are handled in relation to VSC matured packets from the same chain.

### Reasoning - Multiple queues

For reasoning on why this feature was implemented with multiple queues, see [spec](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#consumer-initiated-slashing). Specifically the section on _VSC Maturity and Slashing Order_. There are other ways to ensure such a property (like a queue of linked lists, etc.), but the implemented protocol seemed to be the most understandable and easiest to implement with a KV store.

### Protocol Overview - OnRecvSlashPacket

Upon the provider receiving a slash packet from any of the established consumers during block execution, two things occur:

1. A global slash entry is queued.
2. The data of such a packet is added to the per-chain queue.

### Protocol Overview - OnRecvVSCMaturedPacket

Upon the provider receiving a VSCMatured packet from any of the established consumers during block execution, the VSCMatured packet data is added to the per-chain queue.

### Endblocker Step 1 - Slash Meter Replenishment

Once the slash meter becomes not full, it'll be replenished after `SlashMeterReplenishPeriod (param)` by incrementing the meter with its allowance for the replenishment block, where `allowance` = `SlashMeterReplenishFraction (param)` * `currentTotalVotingPower`. The slash meter will never exceed its current allowance (fn of the total voting power for the block) in value. Note a few things:

1. The slash meter can go negative in value, and will do so when handling a single slash packet that jails a validator with significant voting power. In such a scenario, the slash meter may take multiple replenishment periods to once again reach a positive value (or 0), meaning no other slash packets may be handled for multiple replenishment periods.
2. Total voting power of a chain changes over time, especially as validators are jailed. As validators are jailed, total voting power decreases, and so does the jailing allowance. See below for more detailed throttling property discussion.
3. The voting power allowance added to the slash meter during replenishment will always be greater than or equal to 1. If the `SlashMeterReplenishFraction (param)` is set too low, integer rounding will put this minimum value into effect. That is, if `SlashMeterReplenishFraction` * `currentTotalVotingPower` < 1, then the effective allowance would be 1. This min value of allowance ensures that there's some packets handled over time, even if that is a very long time. It's a crude solution to an edge case caused by too small of a replenishment fraction.

The behavior described above is achieved by executing `CheckForSlashMeterReplenishment()` every endblock, BEFORE `HandleThrottleQueues()` is executed.

### Endblocker Step 2 - HandleLeadingVSCMaturedPackets

Every block it is possible that VSCMatured packet data was queued before any slash packet data. Since this "leading" VSCMatured packet data does not have to be throttled (see _VSC Maturity and Slashing Order_), we can handle all VSCMatured packet data at the head of the queue, before the any throttling or packet data handling logic executes.

### Endblocker Step 3 - HandleThrottleQueues

Every endblocker the following pseudo-code is executed to handle data from the throttle queues.

```typescript
meter := getSlashMeter()

// Keep iterating as long as the meter has a positive (or 0) value, and global slash entries exist 
while meter.IsPositiveOrZero() && entriesExist() {
     // Get next entry in queue
     entry := getNextGlobalSlashEntry()
     // Decrement slash meter by the voting power that will be removed from the valset from handling this slash packet
     valPower := entry.getValPower()
     meter = meter - valPower
     // Using the per-chain queue, handle the single slash packet using its queued data,
     // then handle all trailing VSCMatured packets for this consumer
     handleSlashPacketAndTrailingVSCMaturedPackets(entry)
     // Delete entry in global queue, delete handled data
     entry.Delete()
     deleteThrottledSlashPacketData()
     deleteTrailingVSCMaturedPacketData()
}
```

### System Properties

All CCV system properties should be maintained by implementing this feature, see: [CCV spec - Consumer Initiated Slashing](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#consumer-initiated-slashing).

One implementation-specific property introduced is that if any of the chain-specific packet data queues become larger than `MaxThrottledPackets (param)`, then the provider binary will panic, and the provider chain will halt. Therefore this param should be set carefully. See `SetThrottledPacketDataSize`. This behavior ensures that if the provider binaries are queuing up more packet data than machines can handle, the provider chain halts deterministically between validators.

### Main Throttling Property

Using on-chain params and the sub protocol defined, slash packet throttling is implemented such that the following property holds under some conditions.

First, we define the following:

* A consumer initiated slash attack "starts" when the first slash packet from such an attack is received by the provider.
* The "initial validator set" for the attack is the validator set that existed on the provider when the attack started.
* There is a list of honest validators s.t if they are jailed, `X`% of the initial validator set will be jailed.

For the following property to hold, these assumptions must be true:

1. We assume the total voting power of the chain (as a function of delegations) does not increase over the course of the attack.
2. No validator has more than `SlashMeterReplenishFraction` of total voting power on the provider.
3. `SlashMeterReplenishFraction` is large enough that `SlashMeterReplenishFraction` * `currentTotalVotingPower` > 1. Ie. the replenish fraction is set high enough that we can ignore the effects of rounding.
4. `SlashMeterReplenishPeriod` is sufficiently longer than the time it takes to produce a block.

_Note if these assumptions do not hold, throttling will still slow down the described attack in most cases, just not in a way that can be succinctly described. It's possible that more complex properties can be defined._

Property:

> The time it takes to jail/tombstone `X`% of the initial validator set will be greater than or equal to `(X * SlashMeterReplenishPeriod / SlashMeterReplenishFraction) - 2 * SlashMeterReplenishPeriod`

Intuition:

Let's use the following notation:

* $C$: Number of replenishment cycles
* $P$: $\text{SlashMeterReplenishPeriod}$
* $F$: $\text{SlashMeterReplenishFraction}$
* $V_{\mathit{max}}$: Max power of a validator as a fraction of total voting power

In $C$ number of replenishment cycles, the fraction of total voting power that can be removed, $a$, is $a \leq F \cdot C + V_{\mathit{max}}$ (where $V_{\mathit{max}}$ is there to account for the power fraction of the last validator removed, one which pushes the meter to the negative value).

So, we need at least $C \geq \frac{a - V_{\mathit{max}}}{F}$ cycles to remove $a$ fraction of the total voting power.

Since we defined the start of the attack to be the moment when the first slash request arrives, then $F$ fraction of the initial validator set can be jailed immediately. For the remaining $X - F$ fraction of the initial validator set to be jailed, it takes at least $C \geq \frac{(X - F) - V_{\mathit{max}}}{F}$ cycles. Using the assumption that $V_{\mathit{max}} \leq F$ (assumption 2), we get $C \geq \frac{X - 2F}{F}$ cycles.

In order to execute $C$ cycles, we need $C \cdot P$ time.

Thus, jailing the remaining $X - F$ fraction of the initial validator set corresponds to $\frac{P \cdot (X - 2F)}{F}$ time.

In other words, the attack must take at least $\frac{P \cdot X}{F} - 2P$ time (in the units of replenish period $P$).

This property is useful because it allows us to reason about the time it takes to jail a certain percentage of the initial provider validator set from consumer initiated slash requests. For example, if `SlashMeterReplenishFraction` is set to 0.06, then it takes no less than 4 replenishment periods to jail 33% of the initial provider validator set on the Cosmos Hub. Note that as of writing this on 11/29/22, the Cosmos Hub does not have a validator with more than 6% of total voting power.

Note also that 4 replenishment period is a worst case scenario that depends on well crafted attack timings.

### How Unjailing Affects the Main Throttling Property

Note that the jailing allowance is directly proportional to the current total voting power of the provider chain. Therefore, if honest validators don't unjail themselves during the attack, the total voting power of the provider chain will decrease over the course of the attack, and the attack will be slowed down, main throttling property is maintained.

If honest validators do unjail themselves, the total voting power of the provider chain will still not become higher than when the attack started (unless new token delegations happen), therefore the main property is still maintained. Moreover, honest validators unjailing themselves helps prevent the attacking validators from gaining control of the provider.

In summary, the throttling mechanism as designed has desirable properties whether or not honest validators unjail themselves over the course of the attack.

## Consequences

### Positive

* The described attack is slowed down in seemingly all cases.
* If certain assumptions hold, the described attack is slowed down in a way that can be precisely time-bounded.

### Negative

* Throttling introduces a vector for a malicious consumer chain to halt the provider, see issue below. However, this is sacrificing liveness in a edge case scenario for the sake of security. As an improvement, [using retries](https://github.com/cosmos/interchain-security/issues/713) would fully prevent this attack vector.

### Neutral

* Additional state is introduced to the provider chain.
* VSCMatured and slash packet data is not always handled in the same block that it is received.

## References

* [Original issue inspiring throttling feature](https://github.com/cosmos/interchain-security/issues/404)
* [Issue on DOS vector](https://github.com/cosmos/interchain-security/issues/594)
* [Consideration of another attack vector](https://github.com/cosmos/interchain-security/issues/685)
