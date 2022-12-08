# Slash/VSCMatured Packet Throttling

## Background

The CCV spec is based around the assumption that the provider binary and all consumers binaries are non-malicious, and follow the defined protocols. In practice, this assumption may not hold. A malicious binary could potentially sneak code into a consumer chain which is able to send many downtime or double signing packets at once to the provider.

Without packet throttling, an attacker could then create validators just below the provider's active set, and slash every honest validator at once. These honest validators are then jailed, and control of the chain passes over to the attacker's validators. This enables the attacker to commit arbitrary state on the provider, and to potentially steal all tokens bridged to the provider over IBC.

A solution to this issue is to handle slash packets on the provider such that validators would have more time to notice such an attack scenario is happening. With more time, validators can more effectively respond to the situation compared to everyone getting slashed instantaneously. The implementation in this repo of such a solution is to throttle slash and VSCMatured packets as described below.

## System Properties - CCV

The system properties maintained for CCV are defined here: [CCV spec - Consumer Initiated Slashing](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#consumer-initiated-slashing).

TODO: Update `Provider Slashing Warranty` to accommodate that slash requests are not always applied on the same block that the provider receives a slash packet.

## Data structure - Global entry queue

There exists a single queue which stores "pending slash packet entries". These entries allow the provider to appropriately handle slash packets sent from any consumer in FIFO ordering. This queue is responsible for coordinating the order that slash packets (from multiple chains) are handled over time.

## Data structure - Per-chain data queue

For each established consumer, there exists a queue which stores "pending packet data". Ie. pending slash packet data is queued together with pending VSC matured packet data in FIFO ordering. Order is enforced by IBC sequence number. These "per-chain" queues are responsible for coordinating the order that slash packets are handled in relation to VSC matured packets from the same chain.

## Reasoning - Multiple queues

For reasoning on why this feature was implemented with multiple queues, see [spec](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#consumer-initiated-slashing). Specifically the section on _VSC Maturity and Slashing Order_. There are other ways to ensure such a property (like a queue of linked lists, etc.), but the implemented algorithm seemed to be the most understandable and easiest to implement with a KV store.

## IBC hook - OnRecvSlashPacket

Upon the provider receiving a slash packet from any of the established consumers, two things occur:

1. A pending slash packet entry is queued.
2. The data of such a packet is added to the per-chain queue

## IBC hook - OnRecvVSCMaturedPacket

Upon the provider receiving a VSCMatured packet from any of the established consumers, the following occurs:

1. If the per-chain queue for the consumer that sent this packet is empty, handle the VSC matured packet immediately.
2. Else, add the VSCMatured packet data to the per-chain queue, behind one or more existing packet data instances (which could include slash packet data and/or other VSCMatured packet data)

## Persisted State - Slash Meter

There exists one slash meter on the provider which stores an amount of voting power (integer), corresponding to an allowance of validators that can be jailed/tombstoned over time. This meter is initialized to a certain value on genesis, decremented whenever a slash packet is handled, and periodically replenished as decided by on-chain params.

## Endblocker handling - HandlePendingSlashPackets

Every endblocker the following psuedocode is executed

```typescript
meter := getSlashMeter()

// Keep iterating as long as the meter has positive gas and slash packet entries exist 
while meter.IsPositive() && entriesExist() {
     // Get next entry in queue
     entry := getNextSlashPacketEntry()
     // Decrement slash meter by the voting power that will be removed from the valset from handling this slash packet
     valPower := entry.getValPower()
     meter = meter - valPower
     // Using the per-chain queue, handle the single slash packet using its queued data,
     // then handle all trailing VSCMatured packets for this consumer
     handleSlashPacketAndTrailingVSCMaturedPackets(entry)
     // Delete entry in global queue, delete handled data
     entry.Delete()
     deletePendingSlashPacketData()
     deleteTrailingVSCMaturedPacketData()
}
```

## Endblocker handling - Slash Meter Replenishment

Once the slash meter is not full, it'll be replenished after `SlashMeterReplenishPeriod (param)` by incrementing the meter by its allowance for that period, where `allowance` = `SlashMeterReplenishFraction (param)` * `currentTotalVotingPower`. The slash meter will never exceed its current allowance in value. Note a few things:

1. The slash meter can go negative in value, and will do so when handling a single slash packet that jails a validator with significant voting power. In such a scenario, the slash meter may take multiple replenishment periods to once again reach a positive value, meaning no other slash packets may be handled for multiple replenishment periods.
2. Total voting power of a chain changes over time, especially as validators are jailed/tombstoned. As validators are jailed, total voting power decreases, and so does the slashing allowance per replenishment period.
3. The voting power allowance added to the slash meter per replenish period will always be strictly greater than 1. If the `SlashMeterReplenishFraction (param)` is set too low, integer rounding will put this minimum value into effect.

The behavior described above is achieved by executing `CheckForSlashMeterReplenishment()` every endblock.

## Throttling Invariant

Using on-chain params and the sub protocol defined, slash packet throttling is implemented such that the following invariant is maintained (in addition to those already defined in the CCV spec).

For the following invariant to hold, these points must be true:

- We assume the total voting power of the chain (as a function of delegations) does not significantly increase over the course of the attack.
- The final slashed validator does not have more than `SlashMeterReplenishFraction` of total voting power on the provider.
- `SlashMeterReplenishFraction` is large enough to avoid rounding errors.
- `SlashMeterReplenishPeriod` is sufficiently longer than the time it takes to produce a block.

Invariant:

> If we define a consumer initiated slash attack to start when the first slash packet from such an attack is received by the provider, and we define the initial validator set as the set that existed when the attack started, the time it takes to jail `X`% of the initial validator set will be greater than or equal to `(X * SlashMeterReplenishPeriod / SlashMeterReplenishFraction) - 2 * SlashMeterReplenishPeriod`

Intuition: If jailings begin when the slash meter is full, then `SlashMeterReplenishFraction` of the provider validator set can be jailed immediately. The remaining jailings are only applied when the slash meter is positive in value, so the time it takes to jail the remaining `X - SlashMeterReplenishFraction` of the provider validator set is `(X - SlashMeterReplenishFraction) * SlashMeterReplenishPeriod / SlashMeterReplenishFraction`. However, the final validator could be jailed during the final replenishment period, with the meter being very small in value (causing it to go negative after jailing). So we subtract another `SlashMeterReplenishPeriod` term in the invariant to account for this.

Note this invariant could be adjusted with different slash meter protocols, but the current scheme is the simplest to implement and understand.

This invariant is useful because it allows us to reason about the time it takes to jail a certain percentage of the provider validator set from consumer initiated slash requests. For example, if `SlashMeterReplenishFraction` is set to 0.06, then it takes no less than 4 replenishment periods to jail 33% of the provider validator set on the Cosmos Hub. Note that as of writing this on 11/29/22, the Cosmos Hub does not have a validator with more than 6% of total voting power.

Note also that 4 replenishment period is a worst case scenario that depends on well crafted attack timings.
