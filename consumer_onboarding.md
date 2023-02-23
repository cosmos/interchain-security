# Consumer chain onboarding

## Checklist

### 1. testing & integration
[ ] test integration with gaia
[ ] test your protocol with supported relayer versions (minimum hermes 1.3)
[ ] reach out to ICS team if you are facing issues

### 2. onboarding repository
To help validators and other node runners onboard onto your chain, please prepare a repository with information on how to run your chain.

This should include (at minumum):
[ ] genesis.json witout CCV data (before the propsal passes)
[ ] genesis.json with CCV data (after spawn time passes)
[ ] information about relevant seed/peer nodes you are running
[ ] relayer information (compatible versions)
[ ] copy of your governance proposal (as JSON)
[ ] a script showing how to start your chain and connect to peers (optional)
[ ] take feedback from other developers, validators and community regarding your onboarding repo and make improvements where applicable

Example of such a repository can be found [here](https://github.com/hyphacoop/ics-testnets/tree/main/game-of-chains-2022/sputnik).

### 3. governance proposal

[ ] determine your chain's spawn time
[ ] determine consumer chain parameters to be put in the proposal
[ ] take note to include a link to your onboarding repository
[ ] describe the purpose and benefits of running your chain

Before you submit a proposal, please consider allowing at least a day between your proposal passing and the chain spawn time. This will allow the validators, other node operators and the community to prepare for the chain launch.
If possible, please set your spawn time so people from different parts of the globe can be available in case of emergencies. Ideally, you should set your spawn time to be between 12:00 UTC and 20:00 UTC so most validator operators are available and ready to respond to any issues.

Additionally, reach out to the community via the [forum](https://forum.cosmos.network/) to formalize your intention to become an ICS consumer, gather community support and accept feedback from the community, validators and developers.

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
    // It should should be smaller than that of the provider.
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
}
```

### 4. launch
[ ] provide a repo with onboarding instructions for validators (it should already be listed in the proposal)
[ ] genesis.json with ccv data populated (MUST contain the initial validator set)
[ ] maintenance & emergency contact info (relevant discord, telegram, slack or other communication channels)

The consumer chain starts after at least 66.67% of all provider's voting power comes online. The consumer chain is considered interchain secured once the appropriate CCV channels are established and the first validator set update is propagated from the provider to the consumer


## Developing an ICS consumer chain
When developing an ICS consumer chain, besides just focusing on your chain's logic you should aim to allocate time to ensure that your chain is compatible with the ICS protocol.
To help you on your journey, the ICS team has provied multiple examples of a minumum viable consumer chain applications.

### Basic consumer chain
The source code for the example app can be found [here](https://github.com/cosmos/interchain-security/tree/main/app/consumer).

Please note that consumer chains do not implement the staking module - the validator set is replicated from the provider, meaning that the provider and the consumer use the same validator set and their stake on the provider directly determines their stake on the consumer.
At present there is not an opt-in mechanism available, so all validators of the provider also must validate on the provider chain.

Your chain should import the consumer module from `x/consumer` and register it in the correct places in your `app.go`.
The `x/consumer` module will allow your chain to communicate with the provider using the ICS protocol. The module handles all IBC communication with the provider, and it is a simple drop-in.
You should not need to manage or override any code from the `x/consumer` module.

### Democracy consumer chain
The source code for the example app can be found [here](https://github.com/cosmos/interchain-security/tree/main/app/consumer-democracy).

This type of consumer chain wraps the basic CosmosSDK `x/distribution`, `x/staking` and `x/governance` modules allowing the consumer chain to perform democratic actions such as participating and voting within the chain's governance system.

This allows the consumer chain to leverage those modules while also using the `x/consumer` module.

With these modules enabled, the consumer chain can mint its own governance tokens, which can then be delegated to prominent community members which are referred to as "representatives" (as opposed to "validators" in sovereign chains). The token may have different usecases besides just voting on governance proposals.


## Consumer Chain offboarding

To offboard a consumer chain simply submit a consumer removal proposal listing a `stop_time`. After stop time passes, the provider chain will remove the chain from the ICS protocol (it will stop sending validator set updates).

More information will be listed in a future version of this document.
