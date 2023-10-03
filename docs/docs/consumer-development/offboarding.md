---
sidebar_position: 4
title: Offboarding Checklist
---
# Consumer Offboarding

To offboard a consumer chain simply submit a `ConsumerRemovalProposal` governance proposal listing a `stop_time`. After stop time passes, the provider chain will remove the chain from the ICS protocol (it will stop sending validator set updates).

```js
// ConsumerRemovalProposal is a governance proposal on the provider chain to remove (and stop) a consumer chain.
// If it passes, all the consumer chain's state is removed from the provider chain. The outstanding unbonding
// operation funds are released.
{
    // the title of the proposal
    "title": "This was a great chain",
    "description": "Here is a .md formatted string specifying removal details",
    // the chain-id of the consumer chain to be stopped
    "chain_id": "consumerchain-1",
    // the time on the provider chain at which all validators are responsible to stop their consumer chain validator node
    "stop_time": "2023-03-07T12:40:00.000000Z",
}
```

More information will be listed in a future version of this document.
