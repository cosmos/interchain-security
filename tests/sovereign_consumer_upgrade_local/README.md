## How to run consumer chain

### Pre-install

Binaries:

- interchain-security-pd - [Interchain security](https://github.com/cosmos/interchain-security) version: v0.2.1
- consumerd
- hermes(version: v0.15.0)

### Commands

Copy `start_consumer.sh`, `start_provider.sh` from one of the directories and execute following commands.

```sh
rm -rf /Users/admin/.provider1
rm -rf /Users/admin/.provider
rm -rf /Users/admin/.consumer1
rm -rf /Users/admin/.consumer
rm -rf /Users/admin/.sovereign
sh run.sh
```

### Genesis modification script for consumer chain

```sh
# Add ccv section
if ! ./$PROVIDER_BINARY q provider consumer-genesis "$CONSUMER_CHAIN_ID" --node "$PROVIDER_NODE_ADDRESS" --output json > "$CONSUMER_HOME"/consumer_section.json;
then
       echo "Failed to get consumer genesis for the chain-id '$CONSUMER_CHAIN_ID'! Finalize genesis failed. For more details please check the log file in output directory."
       exit 1
fi

jq -s '.[0].app_state.ccvconsumer = .[1] | .[0]' "$CONSUMER_HOME"/config/genesis.json "$CONSUMER_HOME"/consumer_section.json > "$CONSUMER_HOME"/genesis_consumer.json && \
	mv "$CONSUMER_HOME"/genesis_consumer.json "$CONSUMER_HOME"/config/genesis.json
```

### Process of execution of soft upgrade from sovereign chain to consumer chain

1. Start provider chain and register consumer chain
2. Build normal sovereign chain daemon
3. Start single validator sovereign chain
4. Provider chain validator with sovereign chain
5. Raise Upgrade proposal on sovereign chain and vote
6. Build consumer chain daemon with upgrade handler for ccv module and relevant modules
7. Once chain halt, restart 2 nodes to move from sovereign chain to consumer chain
8. Ensure blocks are being produced without the first node used for sovereign chain
9. Execute delegation on provider chain and ensure consumer chain validators' voting power changes
