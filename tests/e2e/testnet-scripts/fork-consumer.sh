#!/bin/bash
set -eux 

# The gaiad binary
BIN=$1

# the validator ID used to perform the fork
VAL_ID=$2

# The consumer chain ID
CHAIN_ID=$3

# chain's IP address prefix; $PROV_CHAIN_PREFIX, $CONS_CHAIN_PREFIX...
# see chain config for details 
CONS_CHAIN_PREFIX=$4

PROV_CHAIN_PREFIX=$5

VAL_MNEMONIC=$6

FORK_HERMES_CONFIG=$7

FORK_NODE_DIR=/$CHAIN_ID/validatorfork

# create directory for forking/double-signing node
mkdir $FORK_NODE_DIR
cp -r /$CHAIN_ID/validator$VAL_ID/* $FORK_NODE_DIR

# remove persistent peers
rm -f $FORK_NODE_DIR/addrbook.json

# add fork to hermes relayer
tee $FORK_HERMES_CONFIG<<EOF
[global]
log_level = "debug"

[mode]

[mode.clients]
enabled = true
refresh = true
misbehaviour = true

[mode.connections]
enabled = false

[mode.channels]
enabled = false

[mode.packets]
enabled = true

[[chains]]
id = "consu"
ccv_consumer_chain = true
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "tcp://$CONS_CHAIN_PREFIX.252:9091"
key_name = "query"
max_gas = 2000000
rpc_addr = "http://$CONS_CHAIN_PREFIX.252:26658"
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "2days"
websocket_addr = "ws://$CONS_CHAIN_PREFIX.252:26658/websocket"

[chains.gas_price]
        denom = "stake"
        price = 0.00

[chains.trust_threshold]
        denominator = "3"
        numerator = "1"

[[chains]]
id = "provi"
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "tcp://$PROV_CHAIN_PREFIX.4:9091"
key_name = "query"
max_gas = 2000000
rpc_addr = "http://$PROV_CHAIN_PREFIX.4:26658"
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "2days"
websocket_addr = "ws://$PROV_CHAIN_PREFIX.4:26658/websocket"

[chains.gas_price]
        denom = "stake"
        price = 0.00

[chains.trust_threshold]
        denominator = "3"
        numerator = "1"
EOF


echo $VAL_MNEMONIC > mnemonic.txt

# Connecting new peers to Hermes relayer requires somehow to add the account keys again
hermes keys add --mnemonic-file mnemonic.txt --chain consu --overwrite

sleep 1

hermes keys add --mnemonic-file mnemonic.txt --chain provi --overwrite

sleep 1


# Start validator forking the consumer chain by
# reuse the consumer sybil IP allocation
ip netns exec $CHAIN_ID-sybil $BIN \
        --home $FORK_NODE_DIR \
        --address tcp://$CONS_CHAIN_PREFIX.252:26655 \
        --rpc.laddr tcp://$CONS_CHAIN_PREFIX.252:26658 \
        --grpc.address $CONS_CHAIN_PREFIX.252:9091 \
        --log_level info \
        --p2p.laddr tcp://$CONS_CHAIN_PREFIX.252:26656 \
        --grpc-web.enable=false start &> /consu/validatorfork/logs &

