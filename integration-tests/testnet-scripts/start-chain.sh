#!/bin/bash
set -eux

# The gaiad binary
BIN=$1

# JSON array of validator information
# [{
#     mnemonic: "crackle snap pop ... etc",
#     allocation: "10000000000stake,10000000000footoken",
#     stake: "5000000000stake",
#     val_id: "ml", TODO: we have replaced the former "number" field with these two fields. Everywhere that "number" was used in an IP, use ip_suffix. Everywhere that "number" was used in the filesystem, use "val_id".
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

# Get number of nodes from length of validators array
NODES=$(echo "$VALIDATORS" | jq '. | length')




# SETUP NETWORK NAMESPACES

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].number")

    ip netns add $CHAIN_ID-$VAL_ID
    ip link add veth-$CHAIN_ID-$VAL_ID-in type veth peer name veth-$CHAIN_ID-$VAL_ID-out
    ip link set veth-$CHAIN_ID-$VAL_ID-in netns $CHAIN_ID-$VAL_ID
    ip netns exec $CHAIN_ID-$VAL_ID ip addr add $CHAIN_IP_PREFIX.$((VAL_ID+1))/24 dev veth-$CHAIN_ID-$VAL_ID-in
done

ip link add name virtual-bridge type bridge || true

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].number")

    ip link set veth-$CHAIN_ID-$VAL_ID-out master virtual-bridge
done

ip link set virtual-bridge up

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].number")

    ip link set veth-$CHAIN_ID-$VAL_ID-out up
    ip netns exec $CHAIN_ID-$VAL_ID ip link set dev veth-$CHAIN_ID-$VAL_ID-in up
    ip netns exec $CHAIN_ID-$VAL_ID ip link set dev lo up
done

ip addr add $CHAIN_IP_PREFIX.254/24 dev virtual-bridge




# TRANSFORM GENESIS FILE

# first we start a genesis.json with the first validator
# the first validator will also collect the gentx's once gnerated
FIRST_VAL_ID=$(echo "$VALIDATORS" | jq -r ".[0].number")
echo "$VALIDATORS" | jq -r ".[0].mnemonic" | $BIN init --home /$CHAIN_ID/validator$FIRST_VAL_ID --chain-id=$CHAIN_ID validator$FIRST_VAL_ID --recover > /dev/null

# Apply jq transformations to genesis file
jq "$GENESIS_TRANSFORM" /$CHAIN_ID/validator$FIRST_VAL_ID/config/genesis.json > /$CHAIN_ID/edited-genesis.json
mv /$CHAIN_ID/edited-genesis.json /$CHAIN_ID/genesis.json




# CREATE VALIDATOR HOME FOLDERS ETC

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].number")

    # Generate an application key for each validator
    # Sets up an arbitrary number of validators on a single machine by manipulating
    # the --home parameter on gaiad
    echo "$VALIDATORS" | jq -r ".[$i].mnemonic" | $BIN keys add validator$VAL_ID \
        --home /$CHAIN_ID/validator$VAL_ID \
        --keyring-backend test \
        --recover > /dev/null
    
    # Give validators their initial token allocations
    # move the genesis in
    mv /$CHAIN_ID/genesis.json /$CHAIN_ID/validator$VAL_ID/config/genesis.json
    
    # give this validator some money
    ALLOCATION=$(echo "$VALIDATORS" | jq -r ".[$i].allocation")
    $BIN add-genesis-account validator$VAL_ID $ALLOCATION \
        --home /$CHAIN_ID/validator$VAL_ID \
        --keyring-backend test

    # move the genesis back out
    mv /$CHAIN_ID/validator$VAL_ID/config/genesis.json /$CHAIN_ID/genesis.json
done



# MAKE GENTXS AND SET UP LOCAL VALIDATOR STATE

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].number")
    # Copy in the genesis.json
    cp /$CHAIN_ID/genesis.json /$CHAIN_ID/validator$VAL_ID/config/genesis.json

    # Copy in validator state file
    echo '{"height": "0","round": 0,"step": 0}' > /$CHAIN_ID/validator$VAL_ID/data/priv_validator_state.json

    PRIV_VALIDATOR_KEY=$(echo "$VALIDATORS" | jq -r ".[$i].priv_validator_key")
    if [[ "$PRIV_VALIDATOR_KEY" ]]; then
        echo "$PRIV_VALIDATOR_KEY" > /$CHAIN_ID/validator$VAL_ID/config/priv_validator_key.json
    fi

    NODE_KEY=$(echo "$VALIDATORS" | jq -r ".[$i].node_key")
    if [[ "$NODE_KEY" ]]; then
        echo "$NODE_KEY" > /$CHAIN_ID/validator$VAL_ID/config/node_key.json
    fi

    # Make a gentx (this command also sets up validator state on disk even if we are not going to use the gentx for anything)
    if [ "$SKIP_GENTX" = "false" ] ; then 
        STAKE_AMOUNT=$(echo "$VALIDATORS" | jq -r ".[$i].stake")
        $BIN gentx validator$VAL_ID "$STAKE_AMOUNT" \
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
    $BIN collect-gentxs --home /$CHAIN_ID/validator$FIRST_VAL_ID

    # and copy it to the root 
    cp /$CHAIN_ID/validator$FIRST_VAL_ID/config/genesis.json /$CHAIN_ID/genesis.json

    # put the now final genesis.json into the correct folders
    for i in $(seq 1 $(($NODES - 1)));
    do
        VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].number")
        cp /$CHAIN_ID/genesis.json /$CHAIN_ID/validator$VAL_ID/config/genesis.json
    done
fi




# START VALIDATOR NODES

for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].number")
    # add this ip for loopback dialing
    # ip addr add $CHAIN_IP_PREFIX.$VAL_ID/32 dev eth0 || true # allowed to fail

    GAIA_HOME="--home /$CHAIN_ID/validator$VAL_ID"
    RPC_ADDRESS="--rpc.laddr tcp://$CHAIN_IP_PREFIX.$((VAL_ID+1)):26658"
    GRPC_ADDRESS="--grpc.address $CHAIN_IP_PREFIX.$((VAL_ID+1)):9091"
    LISTEN_ADDRESS="--address tcp://$CHAIN_IP_PREFIX.$((VAL_ID+1)):26655"
    P2P_ADDRESS="--p2p.laddr tcp://$CHAIN_IP_PREFIX.$((VAL_ID+1)):26656"
    LOG_LEVEL="--log_level info"
    ENABLE_WEBGRPC="--grpc-web.enable=false"

    PERSISTENT_PEERS=""

    for j in $(seq 0 $(($NODES - 1)));
    do
        if [ $i -ne $j ]; then
            PEER_VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$j].number")
            NODE_ID=$($BIN tendermint show-node-id --home /$CHAIN_ID/validator$PEER_VAL_ID)
            ADDRESS="$NODE_ID@$CHAIN_IP_PREFIX.$((PEER_VAL_ID+1)):26656"
            # (jq -r '.body.memo' /$CHAIN_ID/validator$j/config/gentx/*) # Getting the address from the gentx should also work
            PERSISTENT_PEERS="$PERSISTENT_PEERS,$ADDRESS"
        fi
    done

    # Remove leading comma and concat to flag
    PERSISTENT_PEERS="--p2p.persistent_peers ${PERSISTENT_PEERS:1}"

    ARGS="$GAIA_HOME $LISTEN_ADDRESS $RPC_ADDRESS $GRPC_ADDRESS $LOG_LEVEL $P2P_ADDRESS $ENABLE_WEBGRPC $PERSISTENT_PEERS"
    ip netns exec $CHAIN_ID-$VAL_ID $BIN $ARGS start &> /$CHAIN_ID/validator$VAL_ID/logs &
done




# poll for chain start
set +e
until $BIN query block --node "tcp://$CHAIN_IP_PREFIX.$((FIRST_VAL_ID+1)):26658" | grep -q -v '{"block_id":{"hash":"","parts":{"total":0,"hash":""}},"block":null}'; do sleep 0.3 ; done
set -e

echo "done!!!!!!!!"

read -p "Press Return to Close..."