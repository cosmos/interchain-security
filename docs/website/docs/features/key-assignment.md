# Key Assignment
Key Assignment (aka. as key delegation) allows validator operators to use different consensus keys for each consumer chain validator node that they operate.
There are various reasons to use different consensus keys on different chains, but the main benefit is that validator's provider chain consensus key cannot be compromised if their consumer chain node (or other infrastructure) gets compromised.

The feature is outlined in this [ADR-001](../ADRs/docs/ADRs/adr-001-key-assignment.md)

By sending one transaction, a validator is able to indicate which public key they will be using to validate a consumer chain. Validators can use a different key for each consumer chain. Key assignment is handled only by the provider chain - the consumer chains are not aware of the fact that different consensus keys can represent the same validator entity.

Interchain security modules adds queries and transactions for assigning keys on consumer chains. A key can be assigned before the consumer addition proposal passes.

## Adding a key

First, create a new node on the consumer chain using the equivalent:
```bash
consumerd init <moniker>
```

Then query your node for the consensus key.
```bash
consumerd tendermint show-validator # {"@type":"/cosmos.crypto.ed25519.PubKey","key":"<key>"}
```

Then, make an `assign-consensus-key` transaction on the provider chain in order to inform the provider chain about the consensus key you will be using for a specific consumer chain.

```gaiad tx provider assign-consensus-key <consumer-chain-id> '<pubkey>' \
 --from <tx-signer> \
 --home <home_dir> --gas 900000 -b block -y -o json
```

- `consumer-chain-id` is the string identifier of the consumer chain, as assigned on the provider chain
- `consumer-pub-key` has the following format `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"<key>"}`

Check that the key was assigned correcly by querying the provider:
```bash
gaiad query provider validator-consumer-key <consumer-chain-id> cosmosvalcons1e....3xsj3ayzf4uv6
```

You must use a `valcons` address. You can obtain it by querying your node on the provider `gaiad tendermint show-address`

OR

```bash
gaiad query provider validator-provider-key <consumer-chain-id> consumervalcons1e....123asdnoaisdao
```

You must use a `valcons` address. You can obtain it by querying your node on the consumer `consumerd tendermint show-address`

## Changing a key
To change your key, simply repeat all of the steps listed above. Take note that your old key will be remembered for at least the unbonding period of the consumer chain so any slashes can be correctly applied


## Removing a key
To remove a key, simply switch it back to the consensus key you have assigned on the provider chain by following steps in the `Adding a key` section.
