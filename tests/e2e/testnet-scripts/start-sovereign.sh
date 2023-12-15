#!/bin/bash
set -eux

# The gaiad binary
BIN=$1

# JSON array of validator information
# [{
#     mnemonic: "crackle snap pop ... etc",
#     allocation: "10000000000stake,10000000000footoken",
#     stake: "5000000000stake",
#     val_id: "alice",
#     ip_suffix: "1",
#     priv_validator_key: "{\"address\": \"3566F464673B2F069758DAE86FC25D04017BB147\",\"pub_key\": {\"type\": \"tendermint/PubKeyEd25519\",\"value\": \"XrLjKdc4mB2gfqplvnoySjSJq2E90RynUwaO3WhJutk=\"},\"priv_key\": {\"type\": \"tendermint/PrivKeyEd25519\",\"value\": \"czGSLs/Ocau8aJ5J5zQHMxf3d7NR0xjMECN6YGTIWqtesuMp1ziYHaB+qmW+ejJKNImrYT3RHKdTBo7daEm62Q==\"}}"
#     node_key: "{\"priv_key\":{\"type\":\"tendermint/PrivKeyEd25519\",\"value\":\"alIHj6hXnzpLAadgb7+E2eeecwxoNdzuZrfhMX36EaD5/LgzL0ZUoVp7AK3np0K5T35JWLLv0jJKmeRIhG0GjA==\"}}"
# }, ... ]
VALIDATORS=$2

# The chain ID
CHAIN_ID=$3

# This is the first 3 fields of the IP addresses which will be used internally by the validators of this blockchain
# Recommended to use something starting with 7, since it is squatted by the DoD and is unroutable on the internet
# For example: "7.7.7"
CHAIN_IP_PREFIX=$4

# A transformation to apply to the genesis file, as a jq string
GENESIS_TRANSFORM=$5

# A sed string modifying the tendermint config
TENDERMINT_CONFIG_TRANSFORM=$6

# SETUP NETWORK NAMESPACES, see: https://adil.medium.com/container-networking-under-the-hood-network-namespaces-6b2b8fe8dc2a

# Create virtual bridge device (acts like a switch)
ip link add name virtual-bridge type bridge || true 

# used globally in the whole script
VAL_ID=$(echo "$VALIDATORS" | jq -r ".[0].val_id")
VAL_IP_SUFFIX=$(echo "$VALIDATORS" | jq -r ".[0].ip_suffix")
NET_NAMESPACE_NAME="$CHAIN_ID-$VAL_ID"
IP_ADDR="$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX/24" 

# Create network namespace 
ip netns add $NET_NAMESPACE_NAME
# Create virtual ethernet device to connect with bridge 
ip link add $NET_NAMESPACE_NAME-in type veth peer name $NET_NAMESPACE_NAME-out
# Connect input end of virtual ethernet device to namespace
ip link set $NET_NAMESPACE_NAME-in netns $NET_NAMESPACE_NAME
# Assign ip address to namespace
ip netns exec $NET_NAMESPACE_NAME ip addr add $IP_ADDR dev $NET_NAMESPACE_NAME-in
# Connect output end of virtual ethernet device to bridge
ip link set $NET_NAMESPACE_NAME-out master virtual-bridge

# Enable bridge interface
ip link set virtual-bridge up

NET_NAMESPACE_NAME="$CHAIN_ID-$VAL_ID"
# Enable in/out interfaces for the namespace 
ip link set $NET_NAMESPACE_NAME-out up
ip netns exec $NET_NAMESPACE_NAME ip link set dev $NET_NAMESPACE_NAME-in up
# Enable loopback device
ip netns exec $NET_NAMESPACE_NAME ip link set dev lo up

# Assign IP for bridge, to route between default network namespace and bridge 
BRIDGE_IP="$CHAIN_IP_PREFIX.254/24"
ip addr add $BRIDGE_IP dev virtual-bridge

# first we start a genesis.json with the first validator
# the first validator will also collect the gentx's once generated
echo "$VALIDATORS" | jq -r ".[0].mnemonic" | $BIN init --home /$CHAIN_ID/validator$VAL_ID --chain-id=$CHAIN_ID validator$VAL_ID --recover > /dev/null

# !!!!!!!!! IMPORTANT !!!!!!!!! #
# move the sovereign genesis to the correct validator home dir
cp /testnet-scripts/sovereign-genesis.json /$CHAIN_ID/validator$VAL_ID/config/genesis.json

# Apply jq transformations to genesis file
jq "$GENESIS_TRANSFORM" /$CHAIN_ID/validator$VAL_ID/config/genesis.json > /$CHAIN_ID/edited-genesis.json
mv /$CHAIN_ID/edited-genesis.json /$CHAIN_ID/genesis.json
cp /$CHAIN_ID/genesis.json /$CHAIN_ID/validator$VAL_ID/config/genesis.json



# SETUP LOCAL VALIDATOR STATE
echo '{"height": "0","round": 0,"step": 0}' > /$CHAIN_ID/validator$VAL_ID/data/priv_validator_state.json

PRIV_VALIDATOR_KEY=$(echo "$VALIDATORS" | jq -r ".[0].priv_validator_key")
if [[ "$PRIV_VALIDATOR_KEY" ]]; then
    echo "$PRIV_VALIDATOR_KEY" > /$CHAIN_ID/validator$VAL_ID/config/priv_validator_key.json
fi

NODE_KEY=$(echo "$VALIDATORS" | jq -r ".[0].node_key")
if [[ "$NODE_KEY" ]]; then
    echo "$NODE_KEY" > /$CHAIN_ID/validator$VAL_ID/config/node_key.json
fi

echo "$VALIDATORS" | jq -r ".[0].mnemonic" | $BIN keys add validator$VAL_ID \
--home /$CHAIN_ID/validator$VAL_ID \
--keyring-backend test \
--recover > /dev/null

# Modify tendermint configs of validator
if [ "$TENDERMINT_CONFIG_TRANSFORM" != "" ] ; then 
    #'s/foo/bar/;s/abc/def/'
    sed -i "$TENDERMINT_CONFIG_TRANSFORM" $CHAIN_ID/validator$VAL_ID/config/config.toml
fi


# START VALIDATOR NODE
VAL_IP_SUFFIX=$(echo "$VALIDATORS" | jq -r ".[0].ip_suffix")
NET_NAMESPACE_NAME="$CHAIN_ID-$VAL_ID"

GAIA_HOME="--home /$CHAIN_ID/validator$VAL_ID"
RPC_ADDRESS="--rpc.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26658"
GRPC_ADDRESS="--grpc.address $CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:9091"
LISTEN_ADDRESS="--address tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26655"
P2P_ADDRESS="--p2p.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26656"
# LOG_LEVEL="--log_level trace" # switch to trace to see panic messages and rich and all debug msgs
LOG_LEVEL="--log_level info"
ENABLE_WEBGRPC="--grpc-web.enable=false"

ARGS="$GAIA_HOME $LISTEN_ADDRESS $RPC_ADDRESS $GRPC_ADDRESS $LOG_LEVEL $P2P_ADDRESS $ENABLE_WEBGRPC"
ip netns exec $NET_NAMESPACE_NAME $BIN $ARGS start &> /$CHAIN_ID/validator$VAL_ID/logs &


# poll for chain start
set +e
until $BIN query block --node "tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26658" | grep -q -v '{"block_id":{"hash":"","parts":{"total":0,"hash":""}},"block":null}'; do sleep 0.3 ; done
set -e

echo "done!!!!!!!!"

read -p "Press Return to Close..."