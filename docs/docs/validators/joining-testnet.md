---
sidebar_position: 2
title: Joining Replicated Security testnet
---

# Introduction
This short guide will teach you how to join the [Replicated Security testnet](https://github.com/cosmos/testnets/tree/master/replicated-security).

The experience gained in the testnet will prepare you for validating interchain secured chains.

:::tip
Provider and consumer chain represent distinct networks and infrastructures operated by the same validator set.

For general information about running cosmos-sdk based chains check out the [validator basics](https://hub.cosmos.network/main/validators/validator-setup.html) and [Running a Node section](https://docs.cosmos.network/main/run-node/run-node) of Cosmos SDK docs
:::

# Joining the provider chain
:::info
At present, all validators of the provider chain must also validate all governance approved consumer chains. The consumer chains cannot have a validator set different than the provider, which means they cannot introduce validators that are not also validating the provider chain.
:::

A comprehensive guide is available [here](https://github.com/cosmos/testnets/tree/master/replicated-security/provider).


## Initialization

First, initialize your `$NODE_HOME` using the `provider` chain binary.

```bash
NODE_MONIKER=<your_node>
CHAIN_ID=provider
NODE_HOME=<path_to_your_home>

gaiad init $NODE_MONIKER --chain-id $CHAIN_ID --home $NODE_HOME
```

Add your key to the keyring - more details available [here](https://docs.cosmos.network/main/run-node/keyring).

In this example we will use the `test` keyring-backend. This option is not safe to use in production.
```bash
gaiad keys add <key_moniker> --keyring-backend test

# save the address as variable for later use
MY_VALIDATOR_ADDRESS=$(gaiad keys show my_validator -a --keyring-backend test)
``` 

Before issuing any transactions, use the `provider` testnet faucet to add funds to your address.
```bash
curl https://faucet.rs-testnet.polypore.xyz/request?address=$MY_VALIDATOR_ADDRESS&chain=provider

# example output:
{
    "address": "cosmos17p3erf5gv2436fd4vyjwmudakts563a497syuz",
    "amount": "10000000uatom",
    "chain": "provider",
    "hash": "10BFEC53C80C9B649B66549FD88A0B6BCF09E8FCE468A73B4C4243422E724985",
    "status": "success"
}
```

Then, use the account associated with the keyring to issue a `create-validator` transaction which will register your validator on chain.

```bash
gaiad tx staking create-validator \
  --amount=1000000uatom \
  --pubkey=$(gaiad tendermint show-validator) \
  --moniker="choose a moniker" \
  --chain-id=$CHAIN_ID" \
  --commission-rate="0.10" \
  --commission-max-rate="0.20" \
  --commission-max-change-rate="0.01" \
  --min-self-delegation="1000000" \
  --gas="auto" \
  --gas-prices="0.0025uatom" \
  --from=<key_moniker>
```

:::tip
Check this [guide](https://hub.cosmos.network/main/validators/validator-setup.html#edit-validator-description) to edit your validator.
:::

After this step, your validator is created and you can start your node and catch up to the rest of the network. It is recommended that you use `statesync` to catch up to the rest of the network.

You can use this script to modify your `config.toml` with the required statesync parameters.
```bash
# create the statesync script
$: cd $NODE_HOME
$: touch statesync.sh
$ chmod 700 statesync.sh # make executable
```

Paste the following instructions into the `statesync.sh`:

```bash
#!/bin/bash

SNAP_RPC="https://rpc.provider-state-sync-01.rs-testnet.polypore.xyz:443"

LATEST_HEIGHT=$(curl -s $SNAP_RPC/block | jq -r .result.block.header.height); \
BLOCK_HEIGHT=$((LATEST_HEIGHT - 2000)); \
TRUST_HASH=$(curl -s "$SNAP_RPC/block?height=$BLOCK_HEIGHT" | jq -r .result.block_id.hash)

sed -i.bak -E "s|^(enable[[:space:]]+=[[:space:]]+).*$|\1true| ; \
s|^(rpc_servers[[:space:]]+=[[:space:]]+).*$|\1\"$SNAP_RPC,$SNAP_RPC\"| ; \
s|^(trust_height[[:space:]]+=[[:space:]]+).*$|\1$BLOCK_HEIGHT| ; \
s|^(trust_hash[[:space:]]+=[[:space:]]+).*$|\1\"$TRUST_HASH\"|" $NODE_HOME/config/config.toml
```

Then, you can execute the script:
```bash
$: ./statesync.sh # setup config.toml for statesync
```

Finally, copy the provider genesis and start your node:
```bash
$: GENESIS_URL=https://github.com/cosmos/testnets/raw/master/replicated-security/provider/provider-genesis.json
$: wget $GENESIS_URL -O genesis.json
$: genesis.json $NODE_HOME/config/genesis.json
# start the service
$: gaiad start --x-crisis-skip-assert-invariants --home $NODE_HOME --p2p.seeds="08ec17e86dac67b9da70deb20177655495a55407@provider-seed-01.rs-testnet.polypore.xyz:26656,4ea6e56300a2f37b90e58de5ee27d1c9065cf871@provider-seed-02.rs-testnet.polypore.xyz:26656"
```

Additional scripts to setup your nodes are available [here](https://github.com/cosmos/testnets/blob/master/replicated-security/provider/join-rs-provider.sh) and [here](https://github.com/cosmos/testnets/blob/master/replicated-security/provider/join-rs-provider-cv.sh). The scripts will configure your node and create the required services - the scripts only work in linux environments.

# Joining consumer chains
:::tip
Once you reach the active set on the provider chain, you will be required to validate all available consumer chains.

You can use the same consensus key on all consumer chains, or opt to use a different key on each consumer chain.
Check out this [guide](../features/key-assignment.md) to learn more about key assignment in replicated security.
:::

To join consumer chains, simply replicate the steps above for each consumer using the correct consumer chain binaries.

:::info
When running the provider chain and consumers on the same machine please update the `PORT` numbers for each of them and make sure they do not overlap (otherwise the binaries will not start).

Important ports to re-configure:
- `--rpc.laddr`
- `--p2p.laddr`
- `--api.address`
- `--grpc.address`
- `--grpc-web.address`
:::

## Re-using consensus key
To reuse the key on the provider and consumer chains, simply initialize your consumer chain and place the `priv_validator_key.json` into the home directory of your consumer chain (`<consumer_home>/config/priv_validator_key.json`).

When you start the chain, the consensus key will be the same on the provider and the consumer chain.

## Assigning consensus keys
Whenever you initialize a new node, it will be configured with a consensus key you can use.

```bash
# machine running consumer chain
consumerd init <node_moniker> --home <home_path> --chain-id consumer-1

# use the output of this command to get the consumer chain consensus key
consumerd tendermint show-validator
# output: {"@type":"/cosmos.crypto.ed25519.PubKey","key":"<key>"}
```

Then, let the provider know which key you will be using for the consumer chain:
```bash
# machine running the provider chain
gaiad tx provider assign-consensus-key consumer-1 '<consumer_pubkey>' --from <key_moniker> --home $NODE_HOME --gas 900000 -b block -y -o json
```

After this step, you are ready to copy the consumer genesis into your nodes's `/config` folder, start your consumer chain node and catch up to the network.

## Baryon
<<<<<<< HEAD
You can find the onboarding repo instructions for the Baryon chain [here](https://github.com/cosmos/testnets/blob/master/replicated-security/baryon-1/README.md)


## Noble
You can find the onboarding repo instructions for the Noble chain [here](https://github.com/cosmos/testnets/blob/master/replicated-security/noble-1/README.md)
=======
You can find the onboarding repo instructions for the Baryon chain [here](https://github.com/cosmos/testnets/blob/master/replicated-security/stopped/baryon-1/README.md)

## Noble
You can find the onboarding repo instructions for the Noble chain [here](https://github.com/cosmos/testnets/blob/master/replicated-security/stopped/noble-1/README.md)
>>>>>>> fd76f45 (docs: update broken md links (#1130))
