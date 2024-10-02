---
sidebar_position: 4
title: Offboarding Checklist
---
# Consumer Offboarding

To offboard a consumer chain, the owner of the chain has to submit a `MsgRemoveConsumer` message with the chain's `consumerId`.
If the chain is a Top N chain, the `MsgRemoveConsumer` has to be submitted through a governance proposal.
Otherwise, the message can be submitted simply by the owner of the consumer chain.

When the `MsgRemoveConsumer` executes, the provider chain will stop the chain from the ICS protocol (it will stop
sending validator set updates) and the chain is considered to be in the stopped phase.
At this phase, validators cannot opt in, change keys, etc. and validators stop receiving rewards.
After the chain is stopped, and an unbonding period of time passes, part of the state of the chain is deleted and the chain is considered deleted.
