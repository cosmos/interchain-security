---
sidebar_position: 3
title: Onboarding Checklist
---
# Consumer Onboarding Checklist

The following checklists will aid in onboarding a new consumer chain to replicated security.

Additionally, you can check the [testnet repo](https://github.com/cosmos/testnets/blob/master/replicated-security/CONSUMER_LAUNCH_GUIDE.md) for a comprehensive guide on preparing and launching consumer chains.

## 1. Complete testing & integration

- [ ] test integration with gaia
- [ ] test your protocol with supported relayer versions (minimum hermes 1.4.1)
- [ ] reach out to the ICS team if you are facing issues

## 2. Create an Onboarding Repository

To help validators and other node runners onboard onto your chain, please prepare a repository with information on how to run your chain.

This should include (at minimum):

- [ ] genesis.json without CCV data (before the proposal passes)
- [ ] genesis.json with CCV data (after spawn time passes). Check if CCV data needs to be transformed (see [Transform Consumer Genesis](./consumer-genesis-transformation.md))
- [ ] information about relevant seed/peer nodes you are running
- [ ] relayer information (compatible versions)
- [ ] copy of your governance proposal (as JSON)
- [ ] a script showing how to start your chain and connect to peers (optional)
- [ ] take feedback from other developers, validators and community regarding your onboarding repo and make improvements where applicable

Example of such a repository can be found [here](https://github.com/hyphacoop/ics-testnets/tree/main/game-of-chains-2022/sputnik).

## 3. Submit a Governance Proposal

Before you submit a `ConsumerChainAddition` proposal, please consider allowing at least a day between your proposal passing and the chain spawn time. This will allow the validators, other node operators and the community to prepare for the chain launch.
If possible, please set your spawn time so people from different parts of the globe can be available in case of emergencies. Ideally, you should set your spawn time to be between 12:00 UTC and 20:00 UTC so most validator operators are available and ready to respond to any issues.

Additionally, reach out to the community via the [forum](https://forum.cosmos.network/) to formalize your intention to become an ICS consumer, gather community support and accept feedback from the community, validators and developers.

- [ ] determine your chain's spawn time
- [ ] determine consumer chain parameters to be put in the proposal
- [ ] take note to include a link to your onboarding repository
- [ ] describe the purpose and benefits of running your chain

Example of a consumer chain addition proposal.

```js
// ConsumerAdditionProposal is a governance proposal on the provider chain to spawn a new consumer chain.
// If it passes, then all validators on the provider chain are expected to validate the consumer chain at spawn time.
// It is recommended that spawn time occurs after the proposal end time.
{
    // Title of the proposal
    "title": "Add consumer chain",
    // Description of the proposal
    // format the text as a .md file and include the file in your onboarding repository
    "description": ".md description of your chain and all other relevant information",
    // Proposed chain-id of the new consumer chain.
    // Must be unique from all other consumer chain ids of the executing provider chain.
    "chain_id": "newchain-1",
    // Initial height of new consumer chain.
    // For a completely new chain, this will be {0,1}.
    "initial_height" : {
        "revision_height": 0,
        "revision_number": 1,
    },
    // Hash of the consumer chain genesis state without the consumer CCV module genesis params.
    // It is used for off-chain confirmation of genesis.json validity by validators and other parties.
    "genesis_hash": "d86d756e10118e66e6805e9cc476949da2e750098fcc7634fd0cc77f57a0b2b0",
    // Hash of the consumer chain binary that should be run by validators on chain initialization.
    // It is used for off-chain confirmation of binary validity by validators and other parties.
    "binary_hash": "376cdbd3a222a3d5c730c9637454cd4dd925e2f9e2e0d0f3702fc922928583f1",
    // Time on the provider chain at which the consumer chain genesis is finalized and all validators
    // will be responsible for starting their consumer chain validator node.
    "spawn_time": "2023-02-28T20:40:00.000000Z",
    // Unbonding period for the consumer chain.
    // It should be smaller than that of the provider.
    "unbonding_period": 86400000000000,
    // Timeout period for CCV related IBC packets.
    // Packets are considered timed-out after this interval elapses.
    "ccv_timeout_period": 259200000000000,
    // IBC transfer packets will timeout after this interval elapses.
    "transfer_timeout_period": 1800000000000,
    // The fraction of tokens allocated to the consumer redistribution address during distribution events.
    // The fraction is a string representing a decimal number. For example "0.75" would represent 75%.
    // The reward amount distributed to the provider is calculated as: 1 - consumer_redistribution_fraction.
    "consumer_redistribution_fraction": "0.75",
    // BlocksPerDistributionTransmission is the number of blocks between IBC token transfers from the consumer chain to the provider chain.
    // eg. send rewards to the provider every 1000 blocks
    "blocks_per_distribution_transmission": 1000,
    // The number of historical info entries to persist in store.
    // This param is a part of the cosmos sdk staking module. In the case of
    // a ccv enabled consumer chain, the ccv module acts as the staking module.
    "historical_entries": 10000,
    // The ID of a token transfer channel used for the Reward Distribution
	// sub-protocol. If DistributionTransmissionChannel == "", a new transfer
	// channel is created on top of the same connection as the CCV channel.
	// Note that transfer_channel_id is the ID of the channel end on the consumer chain.
    // it is most relevant for chains performing a sovereign to consumer changeover
    // in order to maintain the existing ibc transfer channel
    "distribution_transmission_channel": "channel-123"
}
```

## 4. Launch

The consumer chain starts after at least 66.67% of all provider's voting power comes online. The consumer chain is considered interchain secured once the appropriate CCV channels are established and the first validator set update is propagated from the provider to the consumer

- [ ] provide a repo with onboarding instructions for validators (it should already be listed in the proposal)
- [ ] genesis.json with ccv data populated (MUST contain the initial validator set)
- [ ] maintenance & emergency contact info (relevant discord, telegram, slack or other communication channels)
- [ ] have a block explorer in place to track chain activity & health
