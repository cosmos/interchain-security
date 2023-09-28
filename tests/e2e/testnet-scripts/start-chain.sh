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

# Whether to skip collecting gentxs so that the genesis does not have them
SKIP_GENTX=$6

# A sed string modifying the tendermint config
TENDERMINT_CONFIG_TRANSFORM=$7

# whether to use CometMock
USE_COMETMOCK=$8

# stores a comma separated list of nodes addresses
# needed for CometMock - these are the addresses that the ABCI servers of the apps are listening on
NODE_LISTEN_ADDR_STR="" # example value: 7.7.8.6:26655,7.7.8.4:26655,7.7.8.5:26655

# stores a comma separated list of nodes home folders
# needed for CometMock - validator nodes have their private keys in their home directories, and CometMock
# reads the keys to sign with from there
NODE_HOMES="" # example value: /consu/validatorcarol,/consu/validatoralice,/consu/validatorbob



# CREATE VALIDATORS AND DO GENESIS CEREMONY

# Get number of nodes from length of validators array
NODES=$(echo "$VALIDATORS" | jq '. | length')

# SETUP NETWORK NAMESPACES, see: https://adil.medium.com/container-networking-under-the-hood-network-namespaces-6b2b8fe8dc2a

# Create virtual bridge device (acts like a switch)
ip link add name virtual-bridge type bridge || true 

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].val_id")
    VAL_IP_SUFFIX=$(echo "$VALIDATORS" | jq -r ".[$i].ip_suffix")
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
done

# Enable bridge interface
ip link set virtual-bridge up

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].val_id")
    NET_NAMESPACE_NAME="$CHAIN_ID-$VAL_ID"

    # Enable in/out interfaces for the namespace 
    ip link set $NET_NAMESPACE_NAME-out up
    ip netns exec $NET_NAMESPACE_NAME ip link set dev $NET_NAMESPACE_NAME-in up
    # Enable loopback device
    ip netns exec $NET_NAMESPACE_NAME ip link set dev lo up
done

# Assign IP for bridge, to route between default network namespace and bridge 
BRIDGE_IP="$CHAIN_IP_PREFIX.254/24"
ip addr add $BRIDGE_IP dev virtual-bridge

# first we start a genesis.json with the first validator
# the first validator will also collect the gentx's once gnerated
FIRST_VAL_ID=$(echo "$VALIDATORS" | jq -r ".[0].val_id")
FIRST_VAL_IP_SUFFIX=$(echo "$VALIDATORS" | jq -r ".[0].ip_suffix")
echo "$VALIDATORS" | jq -r ".[0].mnemonic" | $BIN init --home /$CHAIN_ID/validator$FIRST_VAL_ID --chain-id=$CHAIN_ID validator$FIRST_VAL_ID --recover > /dev/null

# Apply jq transformations to genesis file
jq "$GENESIS_TRANSFORM" /$CHAIN_ID/validator$FIRST_VAL_ID/config/genesis.json > /$CHAIN_ID/edited-genesis.json
mv /$CHAIN_ID/edited-genesis.json /$CHAIN_ID/genesis.json




# CREATE VALIDATOR HOME FOLDERS ETC

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].val_id")
    START_WITH_CONSUMER_KEY=$(echo "$VALIDATORS" | jq -r ".[$i].start_with_consumer_key")
    # Generate an application key for each validator
    # Sets up an arbitrary number of validators on a single machine by manipulating
    # the --home parameter on gaiad
    # optionally start validator with a key different from provider chain key
    if [[ "$CHAIN_ID" != "provi" && "$START_WITH_CONSUMER_KEY" = "true" ]]; then
        echo "$VALIDATORS" | jq -r ".[$i].consumer_mnemonic" | $BIN keys add validator$VAL_ID \
            --home /$CHAIN_ID/validator$VAL_ID \
            --keyring-backend test \
            --recover > /dev/null
    else
        echo "$VALIDATORS" | jq -r ".[$i].mnemonic" | $BIN keys add validator$VAL_ID \
        --home /$CHAIN_ID/validator$VAL_ID \
        --keyring-backend test \
        --recover > /dev/null
    fi
    
    # Give validators their initial token allocations
    # move the genesis in
    mv /$CHAIN_ID/genesis.json /$CHAIN_ID/validator$VAL_ID/config/genesis.json
    
    # give this validator some money
    ALLOCATION=$(echo "$VALIDATORS" | jq -r ".[$i].allocation")
    $BIN genesis add-genesis-account validator$VAL_ID $ALLOCATION \
        --home /$CHAIN_ID/validator$VAL_ID \
        --keyring-backend test

    # move the genesis back out
    mv /$CHAIN_ID/validator$VAL_ID/config/genesis.json /$CHAIN_ID/genesis.json
done



# MAKE GENTXS AND SET UP LOCAL VALIDATOR STATE

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].val_id")

    # Copy in the genesis.json
    cp /$CHAIN_ID/genesis.json /$CHAIN_ID/validator$VAL_ID/config/genesis.json

    # Copy in validator state file
    echo '{"height": "0","round": 0,"step": 0}' > /$CHAIN_ID/validator$VAL_ID/data/priv_validator_state.json

    START_WITH_CONSUMER_KEY=$(echo "$VALIDATORS" | jq -r ".[$i].start_with_consumer_key")
    if [[ "$CHAIN_ID" != "provi" && "$START_WITH_CONSUMER_KEY" = "true" ]]; then
        # start with assigned consumer key
        PRIV_VALIDATOR_KEY=$(echo "$VALIDATORS" | jq -r ".[$i].consumer_priv_validator_key")
        if [[ "$PRIV_VALIDATOR_KEY" ]]; then
            echo "$PRIV_VALIDATOR_KEY" > /$CHAIN_ID/validator$VAL_ID/config/priv_validator_key.json
        fi
    else
        PRIV_VALIDATOR_KEY=$(echo "$VALIDATORS" | jq -r ".[$i].priv_validator_key")
        if [[ "$PRIV_VALIDATOR_KEY" ]]; then
            echo "$PRIV_VALIDATOR_KEY" > /$CHAIN_ID/validator$VAL_ID/config/priv_validator_key.json
        fi
    fi

    NODE_KEY=$(echo "$VALIDATORS" | jq -r ".[$i].node_key")
    if [[ "$NODE_KEY" ]]; then
        echo "$NODE_KEY" > /$CHAIN_ID/validator$VAL_ID/config/node_key.json
    fi

    # Make a gentx (this command also sets up validator state on disk even if we are not going to use the gentx for anything)
    if [ "$SKIP_GENTX" = "false" ] ; then 
        STAKE_AMOUNT=$(echo "$VALIDATORS" | jq -r ".[$i].stake")
        $BIN genesis gentx validator$VAL_ID "$STAKE_AMOUNT" \
            --home /$CHAIN_ID/validator$VAL_ID \
            --keyring-backend test \
            --moniker validator$VAL_ID \
            --chain-id=$CHAIN_ID

        # Copy gentxs to the first validator for possible future collection. 
        # Obviously we don't need to copy the first validator's gentx to itself
        if [ $VAL_ID != $FIRST_VAL_ID ]; then
            cp /$CHAIN_ID/validator$VAL_ID/config/gentx/* /$CHAIN_ID/validator$FIRST_VAL_ID/config/gentx/
        fi
    fi

    # Modify tendermint configs of validator
    if [ "$TENDERMINT_CONFIG_TRANSFORM" != "" ] ; then 
        #'s/foo/bar/;s/abc/def/'
        sed -i "$TENDERMINT_CONFIG_TRANSFORM" $CHAIN_ID/validator$VAL_ID/config/config.toml
    fi

done




# COLLECT GENTXS IF WE ARE STARTING A NEW CHAIN

if [ "$SKIP_GENTX" = "false" ] ; then
    # make the final genesis.json
    $BIN genesis collect-gentxs --home /$CHAIN_ID/validator$FIRST_VAL_ID

    # and copy it to the root 
    cp /$CHAIN_ID/validator$FIRST_VAL_ID/config/genesis.json /$CHAIN_ID/genesis.json

    # put the now final genesis.json into the correct folders
    for i in $(seq 1 $(($NODES - 1)));
    do
        VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].val_id")
        cp /$CHAIN_ID/genesis.json /$CHAIN_ID/validator$VAL_ID/config/genesis.json
    done
fi




# START VALIDATOR NODES

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].val_id")
    VAL_IP_SUFFIX=$(echo "$VALIDATORS" | jq -r ".[$i].ip_suffix")
    NET_NAMESPACE_NAME="$CHAIN_ID-$VAL_ID"

    NODE_HOME="/$CHAIN_ID/validator$VAL_ID"
    GAIA_HOME="--home $NODE_HOME"
    NODE_HOMES="$NODE_HOME,$NODE_HOMES"
    RPC_ADDRESS="--rpc.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26658"
    GRPC_ADDRESS="--grpc.address $CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:9091"
    LISTEN_ADDRESS="--address tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26655"
    NODE_LISTEN_ADDR_STR="$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26655,$NODE_LISTEN_ADDR_STR"
    P2P_ADDRESS="--p2p.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26656"
    # LOG_LEVEL="--log_level trace" # switch to trace to see panic messages and rich and all debug msgs
    LOG_LEVEL="--log_level info"
    ENABLE_WEBGRPC="--grpc-web.enable=false"

    PERSISTENT_PEERS=""

    for j in $(seq 0 $(($NODES - 1)));
    do
        if [ $i -ne $j ]; then
            PEER_VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$j].val_id")
            PEER_VAL_IP_SUFFIX=$(echo "$VALIDATORS" | jq -r ".[$j].ip_suffix")  
            NODE_ID=$($BIN tendermint show-node-id --home /$CHAIN_ID/validator$PEER_VAL_ID)
            ADDRESS="$NODE_ID@$CHAIN_IP_PREFIX.$PEER_VAL_IP_SUFFIX:26656"
            # (jq -r '.body.memo' /$CHAIN_ID/validator$j/config/gentx/*) # Getting the address from the gentx should also work
            PERSISTENT_PEERS="$PERSISTENT_PEERS,$ADDRESS"
        fi
    done

    
    if [ "$PERSISTENT_PEERS" != "" ]; then
        # Remove leading comma and concat to flag
        PERSISTENT_PEERS="--p2p.persistent_peers ${PERSISTENT_PEERS:1}"
    fi
   

    ARGS="$GAIA_HOME $LISTEN_ADDRESS $RPC_ADDRESS $GRPC_ADDRESS $LOG_LEVEL $P2P_ADDRESS $ENABLE_WEBGRPC $PERSISTENT_PEERS"
    if [[ "$USE_COMETMOCK" == "true" ]]; then
        # to start with CometMock, ensure ABCI server  uses grpc (--transport=grpc) and the app is started without in-process CometBFT (--with-tendermint=false)
        ip netns exec $NET_NAMESPACE_NAME $BIN $ARGS start --transport=grpc --with-tendermint=false &> /$CHAIN_ID/validator$VAL_ID/logs &
    else
        ip netns exec $NET_NAMESPACE_NAME $BIN $ARGS start &> /$CHAIN_ID/validator$VAL_ID/logs &
    fi

done

## SETUP DOUBLE SIGNING NODE NETWORK NAMESPACE
# double signing node is started using cause-doublesign.sh
# here we just allocate a network namespace so it can be used later
SYBIL_NODE_ID="sybil"
SYBIL_IP_SUFFIX="252"
SYBIL_NET_NAMESPACE_NAME="$CHAIN_ID-$SYBIL_NODE_ID"
SYBIL_IP_ADDR="$CHAIN_IP_PREFIX.$SYBIL_IP_SUFFIX/24"

ip netns add $SYBIL_NET_NAMESPACE_NAME
ip link add $SYBIL_NET_NAMESPACE_NAME-in type veth peer name $SYBIL_NET_NAMESPACE_NAME-out
ip link set $SYBIL_NET_NAMESPACE_NAME-in netns $SYBIL_NET_NAMESPACE_NAME
ip netns exec $SYBIL_NET_NAMESPACE_NAME ip addr add $SYBIL_IP_ADDR dev $SYBIL_NET_NAMESPACE_NAME-in
ip link set $SYBIL_NET_NAMESPACE_NAME-out master virtual-bridge

## DOUBLE SIGNING ENABLE DEVICE
ip link set $SYBIL_NET_NAMESPACE_NAME-out up
ip netns exec $SYBIL_NET_NAMESPACE_NAME ip link set dev $SYBIL_NET_NAMESPACE_NAME-in up
ip netns exec $SYBIL_NET_NAMESPACE_NAME ip link set dev lo up
## DONE DOUBLE SIGNING NODE ENABLE DEVICE

## SETUP QUERY NODE NETWORK NAMESPACE
QUERY_NODE_ID="query"
QUERY_IP_SUFFIX="253"
QUERY_NET_NAMESPACE_NAME="$CHAIN_ID-$QUERY_NODE_ID"
QUERY_IP_ADDR="$CHAIN_IP_PREFIX.$QUERY_IP_SUFFIX/24"

ip netns add $QUERY_NET_NAMESPACE_NAME
ip link add $QUERY_NET_NAMESPACE_NAME-in type veth peer name $QUERY_NET_NAMESPACE_NAME-out
ip link set $QUERY_NET_NAMESPACE_NAME-in netns $QUERY_NET_NAMESPACE_NAME
ip netns exec $QUERY_NET_NAMESPACE_NAME ip addr add $QUERY_IP_ADDR dev $QUERY_NET_NAMESPACE_NAME-in
ip link set $QUERY_NET_NAMESPACE_NAME-out master virtual-bridge
## DONE ADD SETUP QUERY NODE NETWORK NAMESPACE

## QUERY NODE ENABLE DEVICE
ip link set $QUERY_NET_NAMESPACE_NAME-out up
ip netns exec $QUERY_NET_NAMESPACE_NAME ip link set dev $QUERY_NET_NAMESPACE_NAME-in up
ip netns exec $QUERY_NET_NAMESPACE_NAME ip link set dev lo up
## DONE QUERY NODE ENABLE DEVICE

## INIT QUERY NODE
$BIN init --home /$CHAIN_ID/$QUERY_NODE_ID --chain-id=$CHAIN_ID $QUERY_NODE_ID > /dev/null
cp /$CHAIN_ID/genesis.json /$CHAIN_ID/$QUERY_NODE_ID/config/genesis.json
## DONE INIT QUERY NODE


## START QUERY NODE
QUERY_GAIA_HOME="--home /$CHAIN_ID/$QUERY_NODE_ID"
QUERY_RPC_ADDRESS="--rpc.laddr tcp://$CHAIN_IP_PREFIX.$QUERY_IP_SUFFIX:26658"
QUERY_GRPC_ADDRESS="--grpc.address $CHAIN_IP_PREFIX.$QUERY_IP_SUFFIX:9091"
QUERY_LISTEN_ADDRESS="--address tcp://$CHAIN_IP_PREFIX.$QUERY_IP_SUFFIX:26655"
QUERY_P2P_ADDRESS="--p2p.laddr tcp://$CHAIN_IP_PREFIX.$QUERY_IP_SUFFIX:26656"
# QUERY_LOG_LEVEL="--log_level trace" # switch to trace to see panic messages and rich and all debug msgs
QUERY_LOG_LEVEL="--log_level info"
QUERY_ENABLE_WEBGRPC="--grpc-web.enable=false"

QUERY_PERSISTENT_PEERS=""

## add validators to persistend peers of QUERY node
for j in $(seq 0 $(($NODES - 1)));
do
    PEER_VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$j].val_id")
    PEER_VAL_IP_SUFFIX=$(echo "$VALIDATORS" | jq -r ".[$j].ip_suffix")
    NODE_ID=$($BIN tendermint show-node-id --home /$CHAIN_ID/validator$PEER_VAL_ID)
    ADDRESS="$NODE_ID@$CHAIN_IP_PREFIX.$PEER_VAL_IP_SUFFIX:26656"
    QUERY_PERSISTENT_PEERS="$QUERY_PERSISTENT_PEERS,$ADDRESS"
done

# Remove leading comma and concat to flag
QUERY_PERSISTENT_PEERS="--p2p.persistent_peers ${QUERY_PERSISTENT_PEERS:1}"

## START NODE
ARGS="$QUERY_GAIA_HOME $QUERY_LISTEN_ADDRESS $QUERY_RPC_ADDRESS $QUERY_GRPC_ADDRESS $QUERY_LOG_LEVEL $QUERY_P2P_ADDRESS $QUERY_ENABLE_WEBGRPC $QUERY_PERSISTENT_PEERS"

# Query node is only started if CometMock is not used - with CometMock, it takes the role of the query node
if [[ "$USE_COMETMOCK" != "true" ]]; then
    ip netns exec $QUERY_NET_NAMESPACE_NAME $BIN $ARGS start &> /$CHAIN_ID/$QUERY_NODE_ID/logs &
fi
## DONE START NODE

echo "Node addresses:"
echo $NODE_LISTEN_ADDR_STR

echo "Node homes:"
echo $NODE_HOMES

NODE_LISTEN_ADDR_STR=${NODE_LISTEN_ADDR_STR%?}
NODE_HOMES=${NODE_HOMES%?}


# CometMock takes the role of the query node
if [[ "$USE_COMETMOCK" == "true" ]]; then
    sleep 2
    ip netns exec $QUERY_NET_NAMESPACE_NAME cometmock $NODE_LISTEN_ADDR_STR /$CHAIN_ID/genesis.json tcp://$CHAIN_IP_PREFIX.$QUERY_IP_SUFFIX:26658 $NODE_HOMES grpc &> cometmock_${CHAIN_ID}_out.log &
    sleep 3
fi

# exit



# poll for chain start
if [[ "$USE_COMETMOCK" == "true" ]]; then
    set +e
    until $BIN query block --node "tcp://$CHAIN_IP_PREFIX.$QUERY_IP_SUFFIX:26658"; do sleep 0.3 ; done
    set -e
else
    set +e
    until $BIN query block --node "tcp://$CHAIN_IP_PREFIX.$QUERY_IP_SUFFIX:26658" | grep -q -v '{"block_id":{"hash":"","parts":{"total":0,"hash":
    ""}},"block":null}'; do sleep 0.3 ; done
    set -e
fi

echo "done!!!!!!!!"

read -p "Press Return to Close..."
