#!/bin/bash
set -eux 

TOTAL_COINS=100000000000stake
STAKE_COINS=100000000stake
TOTAL_COINS1=120000000000stake
STAKE_COINS1=1000000stake
PROVIDER_BINARY=interchain-security-pd
PROVIDER_HOME="$HOME/.provider"
PROVIDER_HOME1="$HOME/.provider1"
PROVIDER_CHAIN_ID=provider
PROVIDER_MONIKER=provider
VALIDATOR=validator
VALIDATOR1=validator1
NODE_IP="localhost"
PROVIDER_RPC_LADDR="$NODE_IP:26658"
PROVIDER_GRPC_ADDR="$NODE_IP:9091"
PROVIDER_RPC_LADDR1="$NODE_IP:26668"
PROVIDER_GRPC_ADDR1="$NODE_IP:9101"
PROVIDER_DELEGATOR=delegator

# Clean start
killall $PROVIDER_BINARY &> /dev/null || true

#######VALIDATOR1#######################
rm -rf $PROVIDER_HOME

$PROVIDER_BINARY init $PROVIDER_MONIKER --home $PROVIDER_HOME --chain-id $PROVIDER_CHAIN_ID
jq ".app_state.gov.voting_params.voting_period = \"3s\" | .app_state.staking.params.unbonding_time = \"11600s\" | .app_state.provider.params.template_client.trusting_period = \"11300s\"" \   $PROVIDER_HOME/config/genesis.json > \
   $PROVIDER_HOME/edited_genesis.json && mv $PROVIDER_HOME/edited_genesis.json $PROVIDER_HOME/config/genesis.json
sleep 1

# Create account keypair
$PROVIDER_BINARY keys add $VALIDATOR --home $PROVIDER_HOME --keyring-backend test --output json > $PROVIDER_HOME/keypair.json 2>&1
sleep 1
$PROVIDER_BINARY keys add $PROVIDER_DELEGATOR --home $PROVIDER_HOME --keyring-backend test --output json > $PROVIDER_HOME/keypair_delegator.json 2>&1
sleep 1

# Add stake to user
$PROVIDER_BINARY add-genesis-account $(jq -r .address $PROVIDER_HOME/keypair.json) $TOTAL_COINS --home $PROVIDER_HOME --keyring-backend test
sleep 1
$PROVIDER_BINARY add-genesis-account $(jq -r .address $PROVIDER_HOME/keypair_delegator.json) $TOTAL_COINS --home $PROVIDER_HOME --keyring-backend test
sleep 1

# Stake 1/1000 user's coins
$PROVIDER_BINARY gentx $VALIDATOR $STAKE_COINS --chain-id $PROVIDER_CHAIN_ID --home $PROVIDER_HOME --keyring-backend test --moniker $VALIDATOR
sleep 1

###########VALIDATOR 2############################
rm -rf $PROVIDER_HOME1

$PROVIDER_BINARY init $PROVIDER_MONIKER --home $PROVIDER_HOME1 --chain-id $PROVIDER_CHAIN_ID
cp $PROVIDER_HOME/config/genesis.json $PROVIDER_HOME1/config/genesis.json

# Create account keypair
$PROVIDER_BINARY keys add $VALIDATOR1 --home $PROVIDER_HOME1 --keyring-backend test --output json > $PROVIDER_HOME1/keypair.json 2>&1
sleep 1

# Add stake to user
$PROVIDER_BINARY add-genesis-account $(jq -r .address $PROVIDER_HOME1/keypair.json) $TOTAL_COINS1 --home $PROVIDER_HOME1 --keyring-backend test
sleep 1

####################GENTX AND DISTRIBUTE GENESIS##############################
cp -r  $PROVIDER_HOME/config/gentx $PROVIDER_HOME1/config/

# Stake 1/1000 user's coins
# $PROVIDER_BINARY gentx $VALIDATOR1 $STAKE_COINS1 --chain-id $PROVIDER_CHAIN_ID --home $PROVIDER_HOME1 --keyring-backend test --moniker $VALIDATOR1
# sleep 1

$PROVIDER_BINARY collect-gentxs --home $PROVIDER_HOME1 --gentx-dir $PROVIDER_HOME1/config/gentx/
sleep 1

cp $PROVIDER_HOME1/config/genesis.json $PROVIDER_HOME/config/genesis.json

####################ADDING PEERS####################
node=$($PROVIDER_BINARY tendermint show-node-id --home $PROVIDER_HOME)
node1=$($PROVIDER_BINARY tendermint show-node-id --home $PROVIDER_HOME1)
sed -i -r "/persistent_peers =/ s/= .*/= \"$node@localhost:26656\"/" "$PROVIDER_HOME1"/config/config.toml
sed -i -r "/persistent_peers =/ s/= .*/= \"$node1@localhost:26666\"/" "$PROVIDER_HOME"/config/config.toml

#################### Start the chain node1 ###################
$PROVIDER_BINARY start \
	--home $PROVIDER_HOME \
	--rpc.laddr tcp://$PROVIDER_RPC_LADDR \
	--grpc.address $PROVIDER_GRPC_ADDR \
	--address tcp://${NODE_IP}:26655 \
	--p2p.laddr tcp://${NODE_IP}:26656 \
	--grpc-web.enable=false \
    --trace \
    &> $PROVIDER_HOME/logs &

#################### Start the chain node2 ###################
# $PROVIDER_BINARY start \
# 	--home $PROVIDER_HOME1 \
# 	--rpc.laddr tcp://$PROVIDER_RPC_LADDR1 \
# 	--grpc.address $PROVIDER_GRPC_ADDR1 \
# 	--address tcp://${NODE_IP}:26665 \
# 	--p2p.laddr tcp://${NODE_IP}:26666 \
# 	--grpc-web.enable=false \
#     --trace \
#     &> $PROVIDER_HOME1/logs &
sleep 10

# Build consumer chain proposal file
tee $PROVIDER_HOME/consumer-proposal.json<<EOF
{
    "title": "Create a chain",
    "description": "Gonna be a great chain",
    "chain_id": "consumer",
    "initial_height": {
        "revision_number": 0,
        "revision_height": 9
    },
    "genesis_hash": "519df96a862c30f53e67b1277e6834ab4bd59dfdd08c781d1b7cf3813080fb28",
    "binary_hash": "09184916f3e85aa6fa24d3c12f1e5465af2214f13db265a52fa9f4617146dea5",
    "spawn_time": "2022-06-01T09:10:00.000000000-00:00", 
    "deposit": "10000001stake",
    "consumer_redistribution_fraction": "0.75",
    "blocks_per_distribution_transmission": 1000,
    "ccv_timeout_period": 2419200000000000,
    "transfer_timeout_period": 3600000000000,
    "historical_entries": 10000,
    "unbonding_period": 111200000000000
}
EOF

$PROVIDER_BINARY tx gov submit-proposal consumer-addition $PROVIDER_HOME/consumer-proposal.json \
	--chain-id $PROVIDER_CHAIN_ID --node tcp://$PROVIDER_RPC_LADDR --from $VALIDATOR --home $PROVIDER_HOME --keyring-backend test -b block -y
sleep 1

# Vote yes to proposal
$PROVIDER_BINARY tx gov vote 1 yes --from $VALIDATOR --chain-id $PROVIDER_CHAIN_ID --node tcp://$PROVIDER_RPC_LADDR --home $PROVIDER_HOME -b block -y --keyring-backend test
sleep 5
