#!/bin/bash
set -eux 

# User balance of stake tokens 
USER_COINS="100000000000stake"
# Amount of stake tokens staked
STAKE="100000000stake"
# Node IP address
NODE_IP="127.0.0.1"

# Home directory
HOME_DIR=$HOME

# Validator moniker
MONIKERS=("coordinator" "alice" "bob")
LEAD_VALIDATOR_MONIKER="coordinator"

PROV_NODES_ROOT_DIR=${HOME_DIR}/nodes/provider
CONS_NODES_ROOT_DIR=${HOME_DIR}/nodes/consumer

# Base port. Ports assigned after these ports sequentially by nodes.
RPC_LADDR_BASEPORT=29170
P2P_LADDR_BASEPORT=29180
GRPC_LADDR_BASEPORT=29190
NODE_ADDRESS_BASEPORT=29200
PPROF_LADDR_BASEPORT=29210
CLIENT_BASEPORT=29220

# keeps a comma separated list of node addresses for provider and consumer
PROVIDER_NODE_LISTEN_ADDR_STR=""
CONSUMER_NODE_LISTEN_ADDR_STR=""

PROVIDER_COMETMOCK_ADDR=tcp://$NODE_IP:22331
CONSUMER_COMETMOCK_ADDR=tcp://$NODE_IP:22332

# Clean start
pkill -f interchain-security-pd &> /dev/null || true
pkill -f cometmock &> /dev/null || true
sleep 1
rm -rf ${PROV_NODES_ROOT_DIR}
rm -rf ${CONS_NODES_ROOT_DIR}

# Let lead validator create genesis file
LEAD_VALIDATOR_PROV_DIR=${PROV_NODES_ROOT_DIR}/provider-${LEAD_VALIDATOR_MONIKER}
LEAD_VALIDATOR_CONS_DIR=${CONS_NODES_ROOT_DIR}/consumer-${LEAD_VALIDATOR_MONIKER}
LEAD_PROV_KEY=${LEAD_VALIDATOR_MONIKER}-key
LEAD_PROV_LISTEN_ADDR=tcp://${NODE_IP}:${RPC_LADDR_BASEPORT}

for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}
    # validator key
    PROV_KEY=${MONIKER}-key

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${MONIKER}

    # Build genesis file and node directory structure
    interchain-security-pd init $MONIKER --chain-id provider --home ${PROV_NODE_DIR}
    jq ".app_state.gov.voting_params.voting_period = \"10s\" | .app_state.staking.params.unbonding_time = \"86400s\"" \
    ${PROV_NODE_DIR}/config/genesis.json > \
    ${PROV_NODE_DIR}/edited_genesis.json && mv ${PROV_NODE_DIR}/edited_genesis.json ${PROV_NODE_DIR}/config/genesis.json


    sleep 1

    # Create account keypair
    interchain-security-pd keys add $PROV_KEY --home ${PROV_NODE_DIR} --keyring-backend test --output json > ${PROV_NODE_DIR}/${PROV_KEY}.json 2>&1
    sleep 1

    # copy genesis in, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json ${PROV_NODE_DIR}/config/genesis.json
    fi

    # Add stake to user
    PROV_ACCOUNT_ADDR=$(jq -r '.address' ${PROV_NODE_DIR}/${PROV_KEY}.json)
    interchain-security-pd add-genesis-account $PROV_ACCOUNT_ADDR $USER_COINS --home ${PROV_NODE_DIR} --keyring-backend test
    sleep 1

    # copy genesis out, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${PROV_NODE_DIR}/config/genesis.json ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json
    fi

    PPROF_LADDR=${NODE_IP}:$(($PPROF_LADDR_BASEPORT + $index))
    P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + $index))

    # adjust configs of this node
    sed -i -r 's/timeout_commit = "5s"/timeout_commit = "3s"/g' ${PROV_NODE_DIR}/config/config.toml
    sed -i -r 's/timeout_propose = "3s"/timeout_propose = "1s"/g' ${PROV_NODE_DIR}/config/config.toml

    # make address book non-strict. necessary for this setup
    sed -i -r 's/addr_book_strict = true/addr_book_strict = false/g' ${PROV_NODE_DIR}/config/config.toml

    # avoid port double binding
    sed -i -r  "s/pprof_laddr = \"localhost:6060\"/pprof_laddr = \"${PPROF_LADDR}\"/g" ${PROV_NODE_DIR}/config/config.toml

    # allow duplicate IP addresses (all nodes are on the same machine)
    sed -i -r  's/allow_duplicate_ip = false/allow_duplicate_ip = true/g' ${PROV_NODE_DIR}/config/config.toml
done

for MONIKER in "${MONIKERS[@]}"
do
    # validator key
    PROV_KEY=${MONIKER}-key

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # copy genesis in, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json* ${PROV_NODE_DIR}/config/genesis.json
    fi

    # Stake 1/1000 user's coins
    interchain-security-pd gentx $PROV_KEY $STAKE --chain-id provider --home ${PROV_NODE_DIR} --keyring-backend test --moniker $MONIKER
    sleep 1

    # Copy gentxs to the lead validator for possible future collection. 
    # Obviously we don't need to copy the first validator's gentx to itself
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${PROV_NODE_DIR}/config/gentx/* ${LEAD_VALIDATOR_PROV_DIR}/config/gentx/
    fi
done

# Collect genesis transactions with lead validator
interchain-security-pd collect-gentxs --home ${LEAD_VALIDATOR_PROV_DIR} --gentx-dir ${LEAD_VALIDATOR_PROV_DIR}/config/gentx/

sleep 1


for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}

    PERSISTENT_PEERS=""

    for peer_index in "${!MONIKERS[@]}"
    do
        if [ $index == $peer_index ]; then
            continue
        fi
        PEER_MONIKER=${MONIKERS[$peer_index]}

        PEER_PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${PEER_MONIKER}

        PEER_NODE_ID=$(interchain-security-pd tendermint show-node-id --home ${PEER_PROV_NODE_DIR})

        PEER_P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + $peer_index))
        PERSISTENT_PEERS="$PERSISTENT_PEERS,$PEER_NODE_ID@${NODE_IP}:${PEER_P2P_LADDR_PORT}"
    done

    # remove trailing comma from persistent peers
    PERSISTENT_PEERS=${PERSISTENT_PEERS:1}

    # validator key
    PROV_KEY=${MONIKER}-key

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${PROV_NODES_ROOT_DIR}/consumer-${MONIKER}

    # copy genesis in, unless this validator is already the lead validator and thus it already has its genesis
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json ${PROV_NODE_DIR}/config/genesis.json
    fi

    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + $index))
    P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + $index))
    GRPC_LADDR_PORT=$(($GRPC_LADDR_BASEPORT + $index))
    NODE_ADDRESS_PORT=$(($NODE_ADDRESS_BASEPORT + $index))

    PROVIDER_NODE_LISTEN_ADDR_STR="${NODE_IP}:${NODE_ADDRESS_PORT},$PROVIDER_NODE_LISTEN_ADDR_STR"

    # Start gaia
    interchain-security-pd start \
        --home ${PROV_NODE_DIR} \
        --transport=grpc --with-tendermint=false \
        --p2p.persistent_peers ${PERSISTENT_PEERS} \
        --rpc.laddr tcp://${NODE_IP}:${RPC_LADDR_PORT} \
        --grpc.address ${NODE_IP}:${GRPC_LADDR_PORT} \
        --address tcp://${NODE_IP}:${NODE_ADDRESS_PORT} \
        --p2p.laddr tcp://${NODE_IP}:${P2P_LADDR_PORT} \
        --grpc-web.enable=false &> ${PROV_NODE_DIR}/logs &

    sleep 5
done

PROVIDER_NODE_LISTEN_ADDR_STR=${PROVIDER_NODE_LISTEN_ADDR_STR::${#PROVIDER_NODE_LISTEN_ADDR_STR}-1}

cometmock $PROVIDER_NODE_LISTEN_ADDR_STR ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json $PROVIDER_COMETMOCK_ADDR  &> ${LEAD_VALIDATOR_PROV_DIR}/cometmock_log &

sleep 5

# Build consumer chain proposal file
tee ${LEAD_VALIDATOR_PROV_DIR}/consumer-proposal.json<<EOF
{
    "title": "Create a chain",
    "description": "Gonna be a great chain",
    "chain_id": "consumer",
    "initial_height": {
        "revision_height": 1
    },
    "genesis_hash": "Z2VuX2hhc2g=",
    "binary_hash": "YmluX2hhc2g=",
    "spawn_time": "2023-03-11T09:02:14.718477-08:00",
    "deposit": "10000001stake",
    "consumer_redistribution_fraction": "0.75",
    "blocks_per_distribution_transmission": 1000,
    "historical_entries": 10000,
    "unbonding_period": 864000000000000,
    "ccv_timeout_period": 259200000000000,
    "transfer_timeout_period": 1800000000000
}
EOF

interchain-security-pd keys show $LEAD_PROV_KEY --keyring-backend test --home ${LEAD_VALIDATOR_PROV_DIR}

# Submit consumer chain proposal; use 100* standard gas to ensure we have enough
interchain-security-pd tx gov submit-proposal consumer-addition ${LEAD_VALIDATOR_PROV_DIR}/consumer-proposal.json --chain-id provider --from $LEAD_PROV_KEY --home ${LEAD_VALIDATOR_PROV_DIR} --node $PROVIDER_COMETMOCK_ADDR  --keyring-backend test -b block -y --gas 20000000

sleep 1

# Vote yes to proposal
for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}
    PROV_KEY=${MONIKER}-key
    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + $index))
    RPC_LADDR=tcp://${NODE_IP}:${RPC_LADDR_PORT}

    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}
    interchain-security-pd tx gov vote 1 yes --from $PROV_KEY --chain-id provider --home ${PROV_NODE_DIR} --node $PROVIDER_COMETMOCK_ADDR -b block -y --keyring-backend test
done

# sleep 3

# # ## CONSUMER CHAIN ##

# # Clean start
pkill -f interchain-security-cd &> /dev/null || true
sleep 1
rm -rf ${CONS_NODES_ROOT_DIR}

for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}
    # validator key
    PROV_KEY=${MONIKER}-key

    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${MONIKER}

    # Build genesis file and node directory structure
    interchain-security-cd init $MONIKER --chain-id consumer  --home ${CONS_NODE_DIR}

    sleep 1

    # Create account keypair
    interchain-security-cd keys add $PROV_KEY --home  ${CONS_NODE_DIR} --keyring-backend test --output json > ${CONS_NODE_DIR}/${PROV_KEY}.json 2>&1
    sleep 1

    # copy genesis in, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_CONS_DIR}/config/genesis.json ${CONS_NODE_DIR}/config/genesis.json
    fi

    # Add stake to user
    CONS_ACCOUNT_ADDR=$(jq -r '.address' ${CONS_NODE_DIR}/${PROV_KEY}.json)
    interchain-security-cd add-genesis-account $CONS_ACCOUNT_ADDR $USER_COINS --home ${CONS_NODE_DIR}
    sleep 10

    ### this probably doesnt have to be done for each node
    # Add consumer genesis states to genesis file
    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + $index))
    RPC_LADDR=tcp://${NODE_IP}:${RPC_LADDR_PORT}
    interchain-security-pd query provider consumer-genesis consumer --home ${PROV_NODE_DIR} --node $PROVIDER_COMETMOCK_ADDR -o json > consumer_gen.json
    jq -s '.[0].app_state.ccvconsumer = .[1] | .[0]' ${CONS_NODE_DIR}/config/genesis.json consumer_gen.json > ${CONS_NODE_DIR}/edited_genesis.json \
    && mv ${CONS_NODE_DIR}/edited_genesis.json ${CONS_NODE_DIR}/config/genesis.json
    rm consumer_gen.json
    ###

    # copy genesis out, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${CONS_NODE_DIR}/config/genesis.json ${LEAD_VALIDATOR_CONS_DIR}/config/genesis.json
    fi

    PPROF_LADDR=${NODE_IP}:$(($PPROF_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))
    P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))

    # adjust configs of this node
    sed -i -r 's/timeout_commit = "5s"/timeout_commit = "3s"/g' ${CONS_NODE_DIR}/config/config.toml
    sed -i -r 's/timeout_propose = "3s"/timeout_propose = "1s"/g' ${CONS_NODE_DIR}/config/config.toml

    # make address book non-strict. necessary for this setup
    sed -i -r 's/addr_book_strict = true/addr_book_strict = false/g' ${CONS_NODE_DIR}/config/config.toml

    # avoid port double binding
    sed -i -r  "s/pprof_laddr = \"localhost:6060\"/pprof_laddr = \"${PPROF_LADDR}\"/g" ${CONS_NODE_DIR}/config/config.toml

    # allow duplicate IP addresses (all nodes are on the same machine)
    sed -i -r  's/allow_duplicate_ip = false/allow_duplicate_ip = true/g' ${CONS_NODE_DIR}/config/config.toml

    # Create validator states
    echo '{"height": "0","round": 0,"step": 0}' > ${CONS_NODE_DIR}/data/priv_validator_state.json

    # Copy validator key files
    cp ${PROV_NODE_DIR}/config/priv_validator_key.json ${CONS_NODE_DIR}/config/priv_validator_key.json
    cp ${PROV_NODE_DIR}/config/node_key.json ${CONS_NODE_DIR}/config/node_key.json

    # Set default client port
    CLIENT_PORT=$(($CLIENT_BASEPORT + ${#MONIKERS[@]} + $index))
    sed -i -r "/node =/ s/= .*/= \"tcp:\/\/${NODE_IP}:${CLIENT_PORT}\"/" ${CONS_NODE_DIR}/config/client.toml

done

sleep 1


for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}

    PERSISTENT_PEERS=""

    for peer_index in "${!MONIKERS[@]}"
    do
        if [ $index == $peer_index ]; then
            continue
        fi
        PEER_MONIKER=${MONIKERS[$peer_index]}

        PEER_CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${PEER_MONIKER}

        PEER_NODE_ID=$(interchain-security-pd tendermint show-node-id --home ${PEER_CONS_NODE_DIR})

        PEER_P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + ${#MONIKERS[@]} + $peer_index))
        PERSISTENT_PEERS="$PERSISTENT_PEERS,$PEER_NODE_ID@${NODE_IP}:${PEER_P2P_LADDR_PORT}"
    done

    # remove trailing comma from persistent peers
    PERSISTENT_PEERS=${PERSISTENT_PEERS:1}

    # validator key
    PROV_KEY=${MONIKER}-key

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${MONIKER}

    # copy genesis in, unless this validator is already the lead validator and thus it already has its genesis
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_CONS_DIR}/config/genesis.json ${CONS_NODE_DIR}/config/genesis.json
    fi

    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))
    P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))
    GRPC_LADDR_PORT=$(($GRPC_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))
    NODE_ADDRESS_PORT=$(($NODE_ADDRESS_BASEPORT + ${#MONIKERS[@]} + $index))

    CONSUMER_NODE_LISTEN_ADDR_STR="${NODE_IP}:${NODE_ADDRESS_PORT},$CONSUMER_NODE_LISTEN_ADDR_STR"

    # Start gaia
    interchain-security-cd start \
        --home ${CONS_NODE_DIR} \
        --transport=grpc --with-tendermint=false \
        --p2p.persistent_peers ${PERSISTENT_PEERS} \
        --rpc.laddr tcp://${NODE_IP}:${RPC_LADDR_PORT} \
        --grpc.address ${NODE_IP}:${GRPC_LADDR_PORT} \
        --address tcp://${NODE_IP}:${NODE_ADDRESS_PORT} \
        --p2p.laddr tcp://${NODE_IP}:${P2P_LADDR_PORT} \
        --grpc-web.enable=false &> ${CONS_NODE_DIR}/logs &

    sleep 6
done

# remove trailing comma from consumer node listen addr str
CONSUMER_NODE_LISTEN_ADDR_STR=${CONSUMER_NODE_LISTEN_ADDR_STR::${#CONSUMER_NODE_LISTEN_ADDR_STR}-1}

cometmock $CONSUMER_NODE_LISTEN_ADDR_STR ${LEAD_VALIDATOR_CONS_DIR}/config/genesis.json $CONSUMER_COMETMOCK_ADDR &> ${LEAD_VALIDATOR_CONS_DIR}/cometmock_log &

sleep 5
# # Setup Hermes in packet relayer mode
# pkill -f hermes 2> /dev/null || true

# tee ~/.hermes/config.toml<<EOF
# [global]
# log_level = "info"

# [mode]

# [mode.clients]
# enabled = true
# refresh = true
# misbehaviour = true

# [mode.connections]
# enabled = false

# [mode.channels]
# enabled = false

# [mode.packets]
# enabled = true

# [[chains]]
# account_prefix = "cosmos"
# clock_drift = "5s"
# gas_multiplier = 1.1
# grpc_addr = "tcp://${NODE_IP}:9081"
# id = "consumer"
# key_name = "relayer"
# max_gas = 2000000
# rpc_addr = "http://${NODE_IP}:26648"
# rpc_timeout = "10s"
# store_prefix = "ibc"
# trusting_period = "2days"
# websocket_addr = "ws://${NODE_IP}:26648/websocket"

# [chains.gas_price]
#        denom = "stake"
#        price = 0.00

# [chains.trust_threshold]
#        denominator = "3"
#        numerator = "1"

# [[chains]]
# account_prefix = "cosmos"
# clock_drift = "5s"
# gas_multiplier = 1.1
# grpc_addr = "tcp://${NODE_IP}:9091"
# id = "provider"
# key_name = "relayer"
# max_gas = 2000000
# rpc_addr = "http://${NODE_IP}:26658"
# rpc_timeout = "10s"
# store_prefix = "ibc"
# trusting_period = "2days"
# websocket_addr = "ws://${NODE_IP}:26658/websocket"

# [chains.gas_price]
#        denom = "stake"
#        price = 0.00

# [chains.trust_threshold]
#        denominator = "3"
#        numerator = "1"
# EOF

# # Delete all previous keys in relayer
# hermes keys delete --chain consumer --all
# hermes keys delete --chain provider --all

# # Restore keys to hermes relayer
# hermes keys add --key-file  ${CONS_NODE_DIR}/${PROV_KEY}.json --chain consumer
# hermes keys add --key-file  ${PROV_NODE_DIR}/${PROV_KEY}.json --chain provider


# sleep 5

# hermes create connection \
#      --a-chain consumer \
#     --a-client 07-tendermint-0 \
#     --b-client 07-tendermint-0

# hermes create channel \
#     --a-chain consumer \
#     --a-port consumer \
#     --b-port provider \
#     --order ordered \
#     --channel-version 1 \
#     --a-connection connection-0

# sleep 5

# hermes --json start &> ~/.hermes/logs &

# interchain-security-pd q tendermint-validator-set --home ${PROV_NODE_DIR}
# interchain-security-cd q tendermint-validator-set --home ${CONS_NODE_DIR}

# DELEGATIONS=$(interchain-security-pd q staking delegations $PROV_ACCOUNT_ADDR --home ${PROV_NODE_DIR} -o json)

# OPERATOR_ADDR=$(echo $DELEGATIONS | jq -r '.delegation_responses[0].delegation.validator_address')

# interchain-security-pd tx staking delegate $OPERATOR_ADDR 1000000stake \
#        	--from $PROV_KEY \
#        	--keyring-backend test \
#        	--home ${PROV_NODE_DIR} \
#        	--chain-id provider \
# 	-y -b block

# sleep 13

# interchain-security-pd q tendermint-validator-set --home ${PROV_NODE_DIR}
# interchain-security-cd q tendermint-validator-set --home ${CONS_NODE_DIR}


# # sleep 5

# # tee ${PROV_NODE_DIR}/stop-consumer-proposal.json<<EOF
# # {
# #     "title": "Stop the consumer",
# #     "description": "It was a great chain",
# #     "chain_id": "consumer",
# #     "stop_time": "2022-01-27T15:59:50.121607-08:00",
# #     "deposit": "100000001stake"
# # }
# # EOF

# # # sleep 1

# # interchain-security-pd tx gov submit-proposal stop-consumer-chain \
# # ${PROV_NODE_DIR}/stop-consumer-proposal.json \
# #                             --chain-id provider \
# #                             --from $PROV_KEY \
# #                             --home ${PROV_NODE_DIR} \
# #                             --keyring-backend test \
# #                             -b block -y

# # # sleep 1

# # interchain-security-pd tx gov vote 2 yes \
# #                          --from $PROV_KEY \
# #                          --keyring-backend test \
# #                          --chain-id provider \
# #                          --home $PROV_NODE_DIR \
# #                          -b block -y