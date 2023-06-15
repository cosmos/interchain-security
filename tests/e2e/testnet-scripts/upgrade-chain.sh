#!/bin/bash
set -eux

#########################################################
##                       NOTES                         ##
#########################################################
# The sovereign chain must already be running
# this will swap the old binary for the new binary with
# the same chain-id and the consumer module added

OLD_BIN=$1
NEW_BIN=$2
VALIDATORS=$3
CHAIN_ID=$4
CHAIN_IP_PREFIX=$5

# Get number of nodes from length of validators array
NODES=$(echo "$VALIDATORS" | jq '. | length')

# stop all validator nodes
pkill -f $OLD_BIN &> /dev/null || true

# restart nodes with new binary and wait for a block
for i in $(seq 0 $(($NODES - 1)));
do
    VAL_ID=$(echo "$VALIDATORS" | jq -r ".[$i].val_id")
    VAL_IP_SUFFIX=$(echo "$VALIDATORS" | jq -r ".[$i].ip_suffix")
    NET_NAMESPACE_NAME="$CHAIN_ID-$VAL_ID"

    GAIA_HOME="--home /$CHAIN_ID/validator$VAL_ID"
    RPC_ADDRESS="--rpc.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26658"
    GRPC_ADDRESS="--grpc.address $CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:9091"
    LISTEN_ADDRESS="--address tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26655"
    P2P_ADDRESS="--p2p.laddr tcp://$CHAIN_IP_PREFIX.$VAL_IP_SUFFIX:26656"
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

    # Remove leading comma and concat to flag
    PERSISTENT_PEERS="--p2p.persistent_peers ${PERSISTENT_PEERS:1}"
    ARGS="$GAIA_HOME $LISTEN_ADDRESS $RPC_ADDRESS $GRPC_ADDRESS $LOG_LEVEL $P2P_ADDRESS $ENABLE_WEBGRPC $PERSISTENT_PEERS"

    ip netns exec $NET_NAMESPACE_NAME $NEW_BIN $ARGS start &> /$CHAIN_ID/validator$VAL_ID/logs &
done