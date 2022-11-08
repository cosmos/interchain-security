#!/bin/bash

echo "HAVE $1"

docker exec $1 killall interchain-security-pd interchain-security-cd
docker exec $1 rm -rf /provi/ /consu/ /densu/ /sover/ /democ/
docker exec $1 rm -rf /root/.hermes/keys
docker exec $1 bash -c "echo -e '[global]\n\tlog_level = \"info\"' > /root/.hermes/config.toml"
docker exec $1 bash -c "cat  /dev/null > /root/.hermes/mnemonic.txt"
docker exec $1 hermes keys delete --chain provi --all
docker exec $1 hermes keys delete --chain consu --all
docker exec $1 hermes keys delete --chain densu --all
docker exec $1 hermes keys delete --chain democ --all
docker exec $1 rm -rf .interchain-security-c .interchain-security-p
# clear ip links
docker exec $1 ip -all netns delete
docker exec $1 ip link delete provi-alice-out
docker exec $1 ip link delete provi-bob-out
docker exec $1 ip link delete provi-carol-out
docker exec $1 ip link delete consu-alice-out
docker exec $1 ip link delete consu-bob-out
docker exec $1 ip link delete consu-carol-out
docker exec $1 ip link delete virtual-bridge
