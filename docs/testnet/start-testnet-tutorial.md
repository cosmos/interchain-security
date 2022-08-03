## Interchain Security Testnet

This guide contains the instructions to setup a Interchain-Security Testnet. For the sake of simplicity, both provider and consumer chains run a single node chorum. After the completition of this tutorial you have the possibility to add other nodes to the networks by following these complementary intructions [guide](./join-testnet-tutorial.md).

---

### Prerequisites
- Go 1.18+ <sub><sup>([installation notes](https://go.dev/doc/install))<sub><sup>
- Interchain Security binaries <sub><sup>([installation notes](#install-the-interchain-security-binary))<sub><sup>
- Rust 1.60+ <sub><sup>([installation notes](https://www.rust-lang.org/tools/install))<sub><sup>
- Hermes v1.0.0-rc.1 <sub><sup>([installation notes](https://hermes.informal.systems/getting_started.html))<sub><sup>
- jq  <sub><sup>([installation notes](https://stedolan.github.io/jq/download/))<sub><sup>

---

### Install the Interchain Security Binary
```
git clone https://github.com/cosmos/interchain-security.git
cd interchain-security
make install
```

---

### Install the IBC-Relayer
Follow the instruction to install the IBC-Relayer Rust implementation [here](https://hermes.informal.systems/getting_started.html).

---

### Provider chain setup
The following steps explain how to setup a provider chain running a single validator node. Along this guide we will describe the command arguments and save them using environment variables. 

__0. Remove any existing node directory__  
Start by choosing a directory name, like `~/provider` to store the provider chain node files.

```
PROV-NODE-DIR="~/provider"
rm -rf $PROV-NODE-DIR` <br/><br/>
```

<br/><br/>
    
    
__1. Create an initial genesis__  
The command below initializes the node's configuration files along with a initial genesis file (`${PROV-NODE-DIR}/config/genesis.json`). The `$PROV-NODE-MONIKER` argument is a public moniker that will identify your validator, i.e. `provider-coordinator`). Additionally, in this guide the provider and consumer chains id are self-titled but can be changed arbitrarly.

```
PROV-NODE-MONIKER=provider-coordinator
PROV-CHAIN-ID=provider

interchain-security-pd init $PROV-NODE-MONIKER --chain-id $PROV-CHAIN-ID --home $PROV-NODE-DIR
```  

* *If you want to make any updates to the genesis, it is a good opportunity to make these updates now.*<br/><br/>

<br/><br/>
   
__2. Reduce proposal voting period__  
This command will shorten the voting period to 3 minutes in order to make pass a consumer chain proposal.

```
jq ".app_state.gov.voting_params.voting_period = \"180s\"" \
    ${PROV-NODE-DIR}/config/genesis.json > ${PROV-NODE-DIR}/edited_genesis.json

mv ${PROV-NODE-DIR}/edited_genesis.json ${PROV-NODE-DIR}/config/genesis.json
```  

<br/><br/>

__3. Create an account keypair__  
This following step creates a public/private keypair and stores it under the given keyname of your choice. The output is also exported into a json file for later use.  
```
$PROV-KEY=provider-key
interchain-security-pd keys add $PROV-KEY --home $PROV-NODE-DIR \
    --keyring-backend test --output json > ${PROV-NODE-DIR}/${PROV-KEY}.json 2>&1
```
<br/><br/>

__4. Add funds to account__  
To set an initial account into the genesis states use the command bellow. It will allocates `1000000000` "stake" tokens to our local account.
```
# Get local account address
PROV_ACCOUNT_ADDR=$(jq -r .address ${PROV-NODE-DIR}/${PROV-KEY}.json)

$ Add tokens
interchain-security-pd add-genesis-account $PROV_ACCOUNT_ADDR 1000000000stake \
    --keyring-backend test --home $PROV-NODE-DIR
```
<br/><br/>

__5. Generate a validator transaction__  
To get our validator signing the genesis block (and to agree that this is the correct genesis starting point) and stake `100000000` stake tokens (1/100 of the token balance) executes the following command:  

```
interchain-security-pd gentx $PROV-KEY 100000000stake \
    --keyring-backend test \
    --moniker $PROV-NODE-MONIKER \
    --chain-id $PROV-CHAIN-ID \
    --home $PROV-NODE-DIR
```  

*This command generates a node keypair and use it to sign another "gentx" transaction file. Both files a stored in the `${PROV-NODE-DIR}/config/` folder*   
<br/><br/>

__6. Build the complete genesis__  
This command appends the gentx data into the genesis states.  

```
interchain-security-pd collect-gentxs --home $PROV-NODE-DIR \
    --gentx-dir ${PROV-NODE-DIR}/config/gentx/
```  
<br/><br/>

__7. Setup client RPC endpoint__  
This command changes the default RPC client endpoint port of our node. It is exposed by Tendermint and allows us to query the chains' states and to submit transactions.
    
```
sed -i -r "/node =/ s/= .*/= \"tcp:\/\/localhost:26658\"/" \
    ${PROV-NODE-DIR}/config/client.toml
```
<br/><br/>  

__8. Start the Provider chain__  
Run the local node using the following command:
```
interchain-security-pd start --home $PROV-NODE-DIR \  
        --rpc.laddr tcp://localhost:26658 \ 
        --grpc.address localhost:9091 \  
        --address tcp://localhost:26655 \  
        --p2p.laddr tcp://localhost:26656 \  
        --grpc-web.enable=false \  
        &> ${PROV-NODE-DIR}/logs &
```
*Check the node deamon logs using `tail -f ${PROV-NODE-DIR}/logs`*    

Query the chain to verify your local node appears in the validators list.  

`interchain-security-pd q staking validators --home $PROV-NODE-DIR`

---

### Consumer chain proposal  

These following steps show how to create a consumer chain using the governance and CCV modules enabled in the provider chain we setup before.

__1. Create a consumer chain proposal on the provider__  
Create a governance proposal for a new consumer chain by executing the command above.
```
tee consumer-proposal.json<<EOF
{
    "title": "Create consumer chain",
    "description": "Gonna be a great chain",
    "chain_id": "consumer", 
    "initial_height": {
        "revision_height": 1
    },
    "genesis_hash": "Z2VuX2hhc2g=",
    "binary_hash": "YmluX2hhc2g=",
    "spawn_time": "2022-03-11T09:02:14.718477-08:00",
    "deposit": "10000001stake"
}
EOF
``` 

* *Note that each consumer chain project is expected to have its a different binary and genesis file. Therefore this proposal's `genesis_hash` and `binary_hash` fields are irrelevant in the context of this tutorial. Note that the "spawn_time" should be in the past in order to be able to start the consumer chain immediately.*

<br/><br/>

__2. Submit proposal for the consumer chain to the provider chain__  
This command below will create a governance proposal and allow us to vote for it.
```
#create proposal
interchain-security-pd tx gov submit-proposal \
       create-consumer-chain consumer-proposal.json \
       --keyring-backend test \
       --chain-id $PROV-CHAIN-ID \
       --from $PROV-KEY \
       --home $PROV-NODE-DIR \
       -b block

#vote yes
interchain-security-pd tx gov vote 1 yes --from $PROV-KEY \
       --keyring-backend test --chain-id $PROV-CHAIN-ID --home $PROV-NODE-DIR -b block

#Verify that the proposal status is now `PROPOSAL_STATUS_PASSED`
interchain-security-pd q gov proposal 1 --home $PROV-NODE-DIR
```

---

### Consumer chain setup

This steps show how to setup and to run a consumer chain validator. Note that you must use a different folder to create the consumer chain local node, e.g. ~/consumer.  

__0. Remove network directory__  

```
CONS-NODE-DIR="~/consumer"
rm -rf $CONS-NODE-DIR
```
<br/><br/>  
  
__1. Create an initial genesis__  
Create the initial genesis file (`${CONS-NODE-DIR}/config/genesis.json`) with the following command:
  
```
CONS-NODE-MONIKER=consumer-coordinator
CONS-CHAIN-ID=consumer
interchain-security-cd init $CONS-NODE-MONIKER --chain-id $CONS-CHAIN-ID --home $CONS-NODE-DIR
```  
<br/><br/>

__2. Create an account keypair__  
As for the provider chain, this command below will create an account keypair and store into a json file.

```
$CONS-KEY=consumer-key
interchain-security-cd keys add $CONS-KEY --home $CONS-NODE-DIR \
    --keyring-backend test --output json > ${CONS-NODE-DIR}/${CONS-KEY}.json 2>&1
```  
<br/><br/>

__3. Add account to genesis states__  
To set an initial account into the chain genesis states using the following command. It will allocates `1000000000` "stake" tokens to our local account.

```
#Get local account address
CONS_ACCOUNT_ADDR=$(jq -r .address ${CONS-NODE-DIR}/${CONS-KEY}.json)

#Add account address to genesis
interchain-security-cd add-genesis-account $CONS_ACCOUNT_ADDR 1000000000stake \
    --keyring-backend test --home $CONS-NODE-DIR
 ```  
<br/><br/>  

__4. Get the genesis consumer chain state from the provider chain__  
The CCV genesis states of the consumer chain are retrieved using the query below.  

```
interchain-security-pd query provider consumer-genesis consumer \
    --home $PROV-NODE-DIR -o json > ccvconsumer_genesis.json
```

Insert the CCV states into the initial local node genesis file using this command below.  

```
jq -s '.[0].app_state.ccvconsumer = .[1] | .[0]' ${CONS-NODE-DIR}/config/genesis.json ccvconsumer_genesis.json > \
      ${CONS-NODE-DIR}/edited_genesis.json 

mv ${CONS-NODE-DIR}/edited_genesis.json ${CONS-NODE-DIR}/config/genesis.json
```
<br/><br/>

__5. Copy the validator keypair__  
During the consumer chain initialization, its validator set is populated with the unique provider chain validator. It entails that our consumer chain node is required to run using the same validator info in order to produce blocks. Hence, we have to copy the validator node keypair files into the local consumer chain node folder.

```
echo '{"height": "0","round": 0,"step": 0}' > ${CONS-NODE-DIR}/data/priv_validator_state.json  
cp ${PROV-NODE-DIR}/config/priv_validator_key.json ${CONS-NODE-DIR}/config/priv_validator_key.json  
cp ${PROV-NODE-DIR}/config/node_key.json ${CONS-NODE-DIR}/config/node_key.json
```
 <br/><br/>

__7. Setup client RPC endpoint__  
This command updates the consumer node RPC client config and allow to query the chain states as explained in the [section above](#provider-chain-setup/).  
  
`sed -i -r "/node =/ s/= .*/= \"tcp:\/\/localhost:26648\"/" ${CONS-NODE-DIR}/config/client.toml`
<br/><br/>

__8. Start the Consumer chain__  
Run the local node using the following command:  
```
# consumer local node use the following command
interchain-security-cd start --home $CONS-NODE-DIR \
        --rpc.laddr tcp://localhost:26648 \
        --grpc.address localhost:9081 \
        --address tcp://localhost:26645 \
        --p2p.laddr tcp://localhost:26646 \
        --grpc-web.enable=false \
        &> ${CONS-NODE-DIR}/logs &
```

---
  
__Setup IBC-Relayer__  
These steps guide your through the IBC-Relayer setup in order to have the CCV IBC packet relayed betwen provider and consumer chains.
__1. Create the Hermes configuration file__  
Execute the following comman to create an Hermes relayer config file.  
    
```
tee ~/.hermes/config.toml<<EOF
[global]
 log_level = "info"

[[chains]]
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "tcp://localhost:9081"
id = "$CONS-CHAIN-ID"
key_name = "relayer"
max_gas = 2000000
rpc_addr = "http://localhost:26648"
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "14days"
websocket_addr = "ws://localhost:26648/websocket"

[chains.gas_price]
       denom = "stake"
       price = 0.00

[chains.trust_threshold]
       denominator = "3"
       numerator = "1"

[[chains]]
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "tcp://localhost:9091"
id = "$PROV-CHAIN-ID"
key_name = "relayer"
max_gas = 2000000
rpc_addr = "http://localhost:26658"
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "14days"
websocket_addr = "ws://localhost:26658/websocket"

[chains.gas_price]
       denom = "stake"
       price = 0.00

[chains.trust_threshold]
       denominator = "3"
       numerator = "1"
EOF
```
<br/><br/>
  
__2. Import keypair accounts to the IBC-Relayer__  
Import the acount keypairs to the relayer using the following command.  
```
#Delete all previous keys in relayer
hermes keys delete --chain $CONS-CHAIN-ID --all
hermes keys delete --chain $PROV-CHAIN-ID --all

#Import accounts key
hermes keys add --key-file ${CONS-NODE-DIR}/${CONS-KEY}.json --chain $CONS-CHAIN-ID
hermes keys add --key-file ${PROV-NODE-DIR}/${PROV-KEY}.json --chain $PROV-CHAIN-ID
```

<br/><br/>

__3. Create connection and chanel__  
These commands below establish the IBC connection and channel between the consumer chain and the provider chain.  
```
hermes create connection \
    --a-chain $CONS-CHAIN-ID \
    --a-client 07-tendermint-0 \
    --b-client 07-tendermint-0

hermes create channel \
    --a-chain $CONS-CHAIN-ID \
    --a-port $CONS-CHAIN-ID \
    --b-port  $PROV-CHAIN-ID \
    --order ordered \
    --channel-version 1 \
    --a-connection connection-0
```  
<br/><br/>

__4. Start Hermes__  
The command bellow run the Hermes daemon in listen-mode.  
    
`hermes --json start &> ~/.hermes/logs &`
<br/><br/>

---

### Test the CCV protocol
These optional steps show you how CCV updates the consumer chain validator-set voting power. To do so, delegate some tokens to the validator on the provider chain and verify that the consumer chain validator-set is updated.

__1. Delegate tokens__  
```
# Get validator delegations
DELEGATIONS=$(interchain-security-pd q staking delegations \
  $(jq -r .address ${PROV-NODE-DIR}/<provider_keyname_keypair>.json) --home $PROV-NODE-DIR -o json)

# Get validator operator address
OPERATOR_ADDR=$(echo $DELEGATIONS | jq -r '.delegation_responses[0].delegation.validator_address')

# Delegate tokens
interchain-security-pd tx staking delegate $OPERATOR_ADDR 1000000stake \
                --from $PROV-KEY \
                --keyring-backend test \
                --home $PROV-NODE-DIR \
                --chain-id $PROV-CHAIN-ID \
                -y -b block
```
<br/><br/>

__2. Verify the chains validator-set__  
This commands below will print the updated validator consensus info.

```
# Query provider chain valset
interchain-security-pd q tendermint-validator-set --home $PROV-NODE-DIR
    
# Query consumer chain valset    
interchain-security-cd q tendermint-validator-set --home $CONS-NODE-DIR
```
