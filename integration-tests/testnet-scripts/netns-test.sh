#!/bin/bash
set -eux

CHAIN_ID=$1

CHAIN_IP_PREFIX=$2

# '[{"number": "0"}, {"number": "1"}, {"number": "2"}]'
VALIDATORS=$3

NODES=$(echo "$VALIDATORS" | jq '. | length')

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



# SEE THAT IT WORKS
# ip netns exec 0-0 ping 7.7.7.2
# ip link set veth-0-1-out down
# ip netns exec 0-0 ping 7.7.7.2
# ip link set veth-0-1-out up
# ip netns exec 0-0 ping 7.7.7.2