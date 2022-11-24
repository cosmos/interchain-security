#!/bin/bash

## Key assignment of a previosuly active validator is done as follows:
# - stop node
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

# kill validator node
pkill -f  /$CHAIN_ID/validator$VAL_ID
echo "=================== DONE KILL ==================="

# swap valstate -> validator will sync on restart
echo '{"height": "0","round": 0,"step": 0,"signature":"","signbytes":""}' > /$CHAIN_ID/validator$VAL_ID/data/priv_validator_state.json
echo "=================== DONE STATE ==================="


# swap private key
# echo "$CONSUMER_NODE_KEY" > /$CHAIN_ID/assignvalidator$VAL_ID/config/node_key.json
echo "$CONSUMER_PRIVATE_KEY" > /$CHAIN_ID/validator$VAL_ID/config/priv_validator_key.json
echo "=================== DONE KEY ==================="


# add new key from mnemonic
echo "$CONSUMER_MNEMONIC" | $BIN keys add $CHAIN_ID-validator$VAL_ID --keyring-backend test --home /$CHAIN_ID/validator$VAL_ID --recover  --output json
echo "=================== DONE MNEMO ==================="


# restart node with new key
ARGS="--address tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26655 --rpc.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26658 --grpc.address $CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:9091 --log_level trace --p2p.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26656 --grpc-web.enable=false"
echo "=================== DONE ARGS ==================="

ip netns exec $CHAIN_ID-$VAL_ID $BIN $ARGS start &> /$CHAIN_ID/validator$VAL_ID/logs &
echo "=================== DONE RECONFIGURE $VAL_ID ==================="
