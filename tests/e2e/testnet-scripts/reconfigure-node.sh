#!/bin/bash

## Key assignment of a previously active validator is done as follows:
# - stop node
# - replace config/node_key.json
# - replace config/priv_validator_key.json with keys to use on consumer chain
# - replace config/priv_validator_state.json -> node will need to catch up
# - restart node -> it will use the new key to sign blocks
set -eux


BIN=$1
VAL_ID=$2
CHAIN_ID=$3
CHAIN_IP_PREFIX=$4
VAL_IP_SUFFIX=$5

CONSUMER_MNEMONIC=$6
CONSUMER_PRIVATE_KEY=$7
CONSUMER_NODE_KEY=$8

# kill validator node
pkill -f  /$CHAIN_ID/validator$VAL_ID

# swap valstate -> validator will sync on restart
echo '{"height": "0","round": 0,"step": 0,"signature":"","signbytes":""}' > /$CHAIN_ID/validator$VAL_ID/data/priv_validator_state.json


# swap private key
# echo "$CONSUMER_NODE_KEY" > /$CHAIN_ID/assignvalidator$VAL_ID/config/node_key.json
echo "$CONSUMER_PRIVATE_KEY" > /$CHAIN_ID/validator$VAL_ID/config/priv_validator_key.json

echo "$CONSUMER_NODE_KEY" > /$CHAIN_ID/validator$VAL_ID/config/node_key.json

# remove old key
$BIN keys delete validator$VAL_ID --keyring-backend test --home /$CHAIN_ID/validator$VAL_ID --yes

# add new key from mnemonic
echo "$CONSUMER_MNEMONIC" | $BIN keys add validator$VAL_ID --keyring-backend test --home /$CHAIN_ID/validator$VAL_ID --recover  --output json


# restart node with new key
ARGS="--home /$CHAIN_ID/validator$VAL_ID --address tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26655 --rpc.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26658 --grpc.address $CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:9091 --log_level info --p2p.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26656 --grpc-web.enable=false"

ip netns exec $CHAIN_ID-$VAL_ID $BIN $ARGS start &> /$CHAIN_ID/validator$VAL_ID/logs &

echo 'done!!!!!!!!'
