#!/bin/bash
set -eux

# The gaiad binary
BIN=$1

VAL_ID=$2

# The chain ID
CHAIN_ID=$3

# chain's IP address prefix; 7.7.7, 7.7.8...
# see chain config for details 
CHAIN_PREFIX=${4:-"7.7.7"}

# create directory for double signing node
mkdir /$CHAIN_ID/validatorsybil
cp -r /$CHAIN_ID/validator$VAL_ID/* /$CHAIN_ID/validatorsybil

# clear state in validatorsybil
echo '{"height": "0","round": 0,"step": 0,"signature":"","signbytes":""}' > /$CHAIN_ID/validatorsybil/data/priv_validator_state.json

# add new key to sybil
echo '{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"tj55by/yYwruSz4NxsOG9y9k2WrPvKLXKQdz/9jL9Uptmi647OYpcisjwf92TyA+wCUYVDOgW7D53Q+638l9/w=="}}' > /$CHAIN_ID/validatorsybil/config/node_key.json

# does not use persistent peers; will do a lookup in genesis.json to find peers
ARGS="--address tcp://$CHAIN_PREFIX.252:26655 --rpc.laddr tcp://$CHAIN_PREFIX.252:26658 --grpc.address $CHAIN_PREFIX.252:9091 --log_level trace --p2p.laddr tcp://$CHAIN_PREFIX.252:26656 --grpc-web.enable=false"

# start double signing node - it should not talk to the node with the same key
ip netns exec $CHAIN_ID-sybil $BIN $ARGS --home /$CHAIN_ID/validatorsybil  start &> /$CHAIN_ID/validatorsybil/logs &

