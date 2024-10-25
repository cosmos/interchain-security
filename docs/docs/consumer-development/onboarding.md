---
sidebar_position: 3
title: Onboarding Checklist
---
# Consumer Onboarding Checklist

The following checklists will aid in onboarding a new consumer chain to Interchain Security.

Additionally, you can check the [testnet repo](https://github.com/cosmos/testnets/blob/master/interchain-security/CONSUMER_LAUNCH_GUIDE.md) for a comprehensive guide on preparing and launching consumer chains.

## 1. Complete testing & integration

- [ ] test integration with gaia
- [ ] test your protocol with supported relayer versions (minimum hermes 1.10.2)
- [ ] reach out to the ICS team if you are facing issues

## 2. Create an Onboarding Repository

To help validators and other node runners onboard onto your chain, please prepare a repository with information on how to run your chain.

This should include (at minimum):

- [ ] genesis.json without the consumer module genesis (before the spawn time passes). **Make sure the genesis time is within the trusting period (i.e., one day before launch time or shorter).**
- [ ] genesis.json with the consumer module genesis (after the spawn time passes). Check if the consumer module genesis needs to be transformed (see [Transform Consumer Genesis](./consumer-genesis-transformation.md))
- [ ] information about relevant seed/peer nodes you are running
- [ ] relayer information (compatible versions)
- [ ] a script showing how to start your chain and connect to peers (optional)
- [ ] take feedback from other developers, validators and community regarding your onboarding repo and make improvements where applicable

Example of such a repository can be found [here](https://github.com/hyphacoop/ics-testnets/tree/main/game-of-chains-2022/sputnik).

## 3. Submit `MsgCreateConsumer` (and `MsgUpdateConsumer`) messages

Before you start your chain, you need to submit a `MsgCreateConsumer` message that generates and returns back the
`consumerId` that should be used in any upcoming interactions by the consumer chain or the validators that interact
with your chain. 
Additionally, you need to decide whether your chain should be an Opt-In chain or a Top N chain (see [Partial Set Security](../features/partial-set-security.md))
and act accordingly (see [Permissionless ICS](../features/permissionless.md)).

If you create a Top N chain through, please consider allowing at least a day between your proposal passing and the chain spawn time.
This will allow the validators, other node operators and the community to prepare for the chain launch.
If possible, please set your spawn time so people from different parts of the globe can be available in case of emergencies.
Ideally, you should set your spawn time to be between 12:00 UTC and 20:00 UTC so most validator operators are available and ready to respond to any issues.

Additionally, for a Top N chain, reach out to the community via the [forum](https://forum.cosmos.network/) to formalize your intention to become an ICS consumer,
gather community support and accept feedback from the community, validators and developers.

- [ ] determine your chain's spawn time
- [ ] determine consumer chain parameters
- [ ] take note to include a link to your onboarding repository
- [ ] describe the purpose and benefits of running your chain
- [ ] if desired, decide on power-shaping parameters (see [Power Shaping](../features/power-shaping.md))

Example of initialization parameters:
```js
// ConsumerInitializationParameters provided in MsgCreateConsumer or MsgUpdateConsumer
{
    // Initial height of new consumer chain.
    // For a completely new chain, this will be {1,1}.
    "initial_height" : {
        "revision_height": 1,
        "revision_number": 1,
    },
    // Hash of the consumer chain genesis state without the consumer CCV module genesis params.
    // It is used for off-chain confirmation of genesis.json validity by validators and other parties.
    "genesis_hash": "d86d756e10118e66e6805e9cc476949da2e750098fcc7634fd0cc77f57a0b2b0",
    // Hash of the consumer chain binary that should be run by validators on chain initialization.
    // It is used for off-chain confirmation of binary validity by validators and other parties.
    "binary_hash": "376cdbd3a222a3d5c730c9637454cd4dd925e2f9e2e0d0f3702fc922928583f1",
    // Time on the provider chain at which the consumer chain genesis is finalized and validators
    // will be responsible for starting their consumer chain validator node.
    "spawn_time": "2023-02-28T20:40:00.000000Z",
    // Unbonding period for the consumer chain.
    // It should be smaller than that of the provider.
    "unbonding_period": 1728000000000000,
    // Timeout period for CCV related IBC packets.
    // Packets are considered timed-out after this interval elapses.
    "ccv_timeout_period": 2419200000000000,
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
    // it is most relevant for chains performing a standalone to consumer changeover
    // in order to maintain the existing ibc transfer channel
    "distribution_transmission_channel": "channel-123"
}
```

Example of power-shaping parameters:
```js
// PowerShaping parameters provided in MsgCreateConsumer or MsgUpdateConsumer
{
    // Corresponds to the percentage of validators that have to validate the chain under the Top N case.
    // For example, 53 corresponds to a Top 53% chain, meaning that the top 53% provider validators by voting power
    // have to validate the proposed consumer chain. top_N can either be 0 or any value in [50, 100].
    // A chain can join with top_N == 0 as an Opt In chain, or with top_N ∈ [50, 100] as a Top N chain.
    "top_N": 0,
    // Corresponds to the maximum power (percentage-wise) a validator can have on the consumer chain. For instance, if
    // `validators_power_cap` is set to 32, it means that no validator can have more than 32% of the voting power on the
    // consumer chain. Note that this might not be feasible. For example, think of a consumer chain with only
    // 5 validators and with `validators_power_cap` set to 10%. In such a scenario, at least one validator would need
    // to have more than 20% of the total voting power. Therefore, `validators_power_cap` operates on a best-effort basis.
    "validators_power_cap": 0,
    // Corresponds to the maximum number of validators that can validate a consumer chain.
    // Only applicable to Opt In chains. Setting `validator_set_cap` on a Top N chain is a no-op.
    "validator_set_cap": 0,
    // Corresponds to a list of provider consensus addresses of validators that are the ONLY ones that can validate
    // the consumer chain.
    "allowlist": ["cosmosvalcons..."],
    // Corresponds to a list of provider consensus addresses of validators that CANNOT validate the consumer chain.
    "denylist": ["cosmosvalcons..."],
    // Corresponds to the minimal amount of (provider chain) stake required to validate on the consumer chain.
    "min_stake": 0,
    // Corresponds to whether inactive validators are allowed to validate the consumer chain.
    "allow_inactive_vals": false,
    // Corresponds to a list of provider consensus addresses of validators that have priority
    "prioritylist": [],
}
```

Example of allowlisted reward denoms:
```js
// AllowlistedRewardDenoms provided in MsgCreateConsumer or MsgUpdateConsumer
{
    "denoms": ["ibc/0025F8A87464A471E66B234C4F93AEC5B4DA3D42D7986451A059273426290DD5", "ibc/054892D6BB43AF8B93AAC28AA5FD7019D2C59A15DAFD6F45C1FA2BF9BDA22454"]
}
```

:::caution
For opt-in consumer chains, make sure that at least one validator opts in before the spawn time elapses.
Otherwise the launch process will be aborted and the spawn time needs to be updated by submitting a `MsgUpdateConsumer` message.
:::

## 4. Launch

The consumer chain starts after at least 66.67% of its voting power comes online.
Note that this means 66.67% of the voting power in the *consumer* validator set, which will be comprised of all validators that either opted in to the chain or are part of the top N% of the provider chain (and are thus automatically opted in).
The consumer chain is considered interchain secured once the appropriate CCV channels are established and the first validator set update is propagated from the provider to the consumer

- [ ] provide a repo with onboarding instructions for validators
- [ ] genesis.json with the consumer module section populated (MUST contain the initial validator set)
- [ ] maintenance & emergency contact info (relevant discord, telegram, slack or other communication channels)
- [ ] have a block explorer in place to track chain activity & health

### Establish CCV channel 

Once the consumer chain is launched, the CCV channel needs to be established. The following instructions are setting both the connection and channel using Hermes:

```bash
#!/bin/bash

# CONSUMER_CLIENT_ID is created on CONSUMER upon genesis
CONSUMER_CLIENT_ID="<consumer-client-id>"
CONSUMER_CHAIN_ID="<consumer-chain-id>"

# PROVIDER_CLIENT_ID is created on PROVIDER upon CONSUMER spawn time: gaiad q provider list-consumer-chains
PROVIDER_CLIENT_ID="<provider-client-id>"
PROVIDER_CHAIN_ID="<provider-chain-id>"

CONFIG=$1
if [ -z "$CONFIG" ]; then 
    CONFIG=$HOME/.hermes/config.toml
fi
if [ ! -f "$CONFIG" ]; then
    echo "no config file found at $CONFIG"
    exit 1
fi

output=$(hermes --json --config $CONFIG create connection --a-chain $CONSUMER_CHAIN_ID --a-client $CONSUMER_CLIENT_ID --b-client $PROVIDER_CLIENT_ID | tee /dev/tty)
json_output=$(echo "$output" | grep 'result')
a_side_connection_id=$(echo "$json_output" | jq -r '.result.a_side.connection_id')
output=$(hermes --json --config $CONFIG create channel --a-chain $CONSUMER_CHAIN_ID --a-port consumer --b-port provider --order ordered --a-connection $a_side_connection_id --channel-version 1 | tee /dev/tty)
json_output=$(echo "$output" | grep 'result')
echo "---- DONE ----"
echo "$json_output" | jq

# hermes start
```
