## Interchain-Security Testnet

This guide contains the instructions to setup a Interchain-Security Testnet. For the sake of simplicity, both provider and consumer chains run a single node chorum. After the completition of this tutorial you have the possibility to add other nodes to the networks by following these complementary intructions [guide](https://github.com/sainoe/IS-testnet/blob/main/join-is-tesnet.md).

---

### Prerequisites
- Go 1.18+ <sub><sup>([installation notes](https://go.dev/doc/install))<sub><sup>
- Interchain-Security binaries
- Rust 1.60+ <sub><sup>([installation notes](https://www.rust-lang.org/tools/install))<sub><sup>
- Hermes v1.0.0-rc.0
- jq

---

### Install the IS Binary
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
The following steps explain how to setup a provider chain running a single validator node. Choose a directory name `/<prov-node-dir>` (e.g. `~/provider`) to store the provider chain node files. Along this guide, the provider and consumer chain ids used are respectively `provider` and `consumer`.

__0. Remove any existing node directory__

`rm -rf /<prov-node-dir>`<br/><br/>

__1. Create an initial genesis__  
Create the initial genesis file (`/<prov-node-dir>/config/genesis.json`) with the following command:  

`interchain-security-pd init <provider-node-moniker> --chain-id provider --home /<prov-node-dir>`  

*If you want to make any updates to the genesis, it is a good opportunity to make these updates now.*<br/><br/>

__2. Reduce proposal voting period__  
This command will shorten the voting period to 3 minutes in order to make pass a consumer chain proposal.

```
jq ".app_state.gov.voting_params.voting_period = \"180s\"" \
    /<prov-node-dir>/config/genesis.json > /<prov-node-dir>/edited_genesis.json

mv /<prov-node-dir>/edited_genesis.json /<prov-node-dir>/config/genesis.json
```  
<br/><br/>

__3. Create an account keypair__  
This following step creates a public/private keypair and stores it under the given keyname. The output is also exported into a json file for later use.  
```
interchain-security-pd keys add <provider-keyname> --home /<prov-node-dir> \
    --keyring-backend test --output json > /<prov-node-dir>/<provider_keyname_keypair.json> 2>&1
```
<br/><br/>

__4. Add funds to account__  
To set an initial account into the genesis states use the command bellow. It will allocates `1000000000` "stake" tokens to our local account.
```
# Get local account address
PROV_ACCOUNT_ADDR=$(jq -r .address /<prov-node-dir>/<provider_keyname_keypair.json>)

$ Add tokens
interchain-security-pd add-genesis-account $PROV_ACCOUNT_ADDR 1000000000stake \
    --keyring-backend test --home /<prov-node-dir>
```
<br/><br/>

__5. Generate a validator transaction__  
To get our validator signing the genesis block (and to agree that this is the correct genesis starting point) and stake `100000000` stake tokens (1/100 of the token balance) executes the following command:  

```
interchain-security-pd gentx <provider-keyname> 100000000stake \
    --keyring-backend test \
    --moniker <provider-node-moniker> \
    --chain-id provider \
    --home /<prov-node-dir>
```  

*This command generates a node keypair and use it to sign another "gentx" transaction file. Both files a stored in the `/<prov-node-dir>/config/` folder*   
<br/><br/>

__6. Build the complete genesis__  
This command appends the gentx data into the genesis states.  

```
interchain-security-pd collect-gentxs --home /<prov-node-dir> \
    --gentx-dir /<prov-node-dir>/config/gentx/
```  
<br/><br/>

__7. Setup client RPC endpoint__  
This  command updates the consumer node RPC client config and allow to query the chain states.  
    
```
sed -i -r "/node =/ s/= .*/= \"tcp:\/\/localhost:26658\"/" \
    /<prov-node-dir>/config/client.toml
```
<br/><br/>  

__8. Start the Provider chain__  
Run the local node using the following command:
```
interchain-security-pd start --home /<prov-node-dir> \  
        --rpc.laddr tcp://localhost:26658 \ 
        --grpc.address localhost:9091 \  
        --address tcp://localhost:26655 \  
        --p2p.laddr tcp://localhost:26656 \  
        --grpc-web.enable=false \  
        &> /<prov-node-dir>/logs &
```
*Check the node deamon logs using `tail -f /<prov-node-dir>/logs`*    

Query the chain to verify your local node appears in the validators list.  

`interchain-security-pd q staking validators --home /<prov-node-dir>`

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
<br/><br/>
__2. Submit proposal for the consumer chain to the provider chain__  
This command below will create a governance proposal and allow us to vote for it.
```
#create proposal
interchain-security-pd tx gov submit-proposal \
       create-consumer-chain consumer-proposal.json \
       --keyring-backend test \
       --chain-id provider \
       --from <provider-keyname> \
       --home /<prov-node-dir> \
       -b block

#vote yes
interchain-security-pd tx gov vote 1 yes --from <provider-keyname> \
       --keyring-backend test --chain-id provider --home /<prov-node-dir> -b block

#Verify that the proposal status is now `PROPOSAL_STATUS_PASSED`
interchain-security-pd q gov proposal 1 --home /<prov-node-dir>
```

---

### Consumer chain setup

This steps show how to setup and to run a consumer chain validator. Note that you must use a different folder to create the consumer chain local node (<cons-node-dir> e.g. /consumer).  

__0. Remove network directory__  

`rm -rf /<cons-node-dir>`
<br/><br/>  
  
__1. Create an initial genesis__  
Create the initial genesis file (`/<cons-node-dir>/config/genesis.json`) with the following command:
  
`interchain-security-cd init <consumer-node-moniker> --chain-id consumer  --home /<cons-node-dir>`  
<br/><br/>

__2. Create an account keypair__  
As for the provider chain, this command below will create an account keypair and store into a json file.

```
interchain-security-cd keys add <consumer-keyname> --home /<cons-node-dir> \
    --keyring-backend test --output json > /<cons-node-dir>/<consumer_keyname_keypair>.json 2>&1
```  
<br/><br/>

__3. Add account to genesis states__  
To set an initial account into the chain genesis states using the following command. It will allocates `1000000000` "stake" tokens to our local account.

```
#Get local account address
CONS_ACCOUNT_ADDR=$(jq -r .address /<cons-node-dir>/<consumer_keyname_keypair>.json)

#Add account address to genesis
interchain-security-cd add-genesis-account $CONS_ACCOUNT_ADDR 1000000000stake \
    --keyring-backend test --home /<cons-node-dir>
 ```  
<br/><br/>  

__4. Get the genesis consumer chain state from the provider chain__  
The CCV genesis states of the consumer chain are retrieved using the query below.  

```
interchain-security-pd query provider consumer-genesis consumer \
    --home /<prov-node-dir> -o json > ccvconsumer_genesis.json
```

Insert the CCV states into the initial local node genesis file using this command below.  

```
jq -s '.[0].app_state.ccvconsumer = .[1] | .[0]' /<cons-node-dir>/config/genesis.json ccvconsumer_genesis.json > \
      /<cons-node-dir>/edited_genesis.json 

mv /<cons-node-dir>/edited_genesis.json /<cons-node-dir>/config/genesis.json
```
<br/><br/>

__5. Copy the validator keypair__  
During the consumer chain initialization, its validator set is populated with the unique provider chain validator. It entails that our consumer chain node is required to run using the same validator info in order to produce blocks. Hence, we have to copy the validator node keypair files into the local consumer chain node folder.

```
echo '{"height": "0","round": 0,"step": 0}' > /<cons-node-dir>/data/priv_validator_state.json  
cp /<prov-node-dir>/config/priv_validator_key.json <cons-node-dir>/config/priv_validator_key.json  
cp /<prov-node-dir>/config/node_key.json /<cons-node-dir>/config/node_key.json
```
 <br/><br/>

__7. Setup client RPC endpoint__  
This  command updates the consumer node RPC client config and allow to query the chain states.  
  
`sed -i -r "/node =/ s/= .*/= \"tcp:\/\/localhost:26648\"/" /<cons-node-dir>/config/client.toml`
<br/><br/>

__8. Start the Consumer chain__  
Run the local node using the following command:  
```
# consumer local node use the following command
interchain-security-cd start --home /<cons-node-dir> \
        --rpc.laddr tcp://localhost:26648 \
        --grpc.address localhost:9081 \
        --address tcp://localhost:26645 \
        --p2p.laddr tcp://localhost:26646 \
        --grpc-web.enable=false \
        &> /<cons-node-dir>/logs &
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
id = "consumer"
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
id = "provider"
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
hermes keys delete --chain consumer --all
hermes keys delete --chain provider --all

#Import accounts key
hermes keys add --key-file /<cons-node-dir>/<consumer_keyname_keypair>.json --chain consumer
hermes keys add --key-file /<prov-node-dir>/<provider_keyname_keypair>.json --chain provider
```

<br/><br/>

__3. Create connection and chanel__  
These commands below establish the IBC connection and channel between the consumer chain and the provider chain.  
```
hermes create connection \
    --a-chain consumer \
    --a-client 07-tendermint-0 \
    --b-client 07-tendermint-0

hermes create channel \
    --a-chain consumer \
    --a-port consumer \
    --b-port provider \
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
  $(jq -r .address /<prov-node-dir>/<provider_keyname_keypair>.json) --home /<prov-node-dir> -o json)

# Get validator operator address
OPERATOR_ADDR=$(echo $DELEGATIONS | jq -r '.delegation_responses[0].delegation.validator_address')

# Delegate tokens
interchain-security-pd tx staking delegate $OPERATOR_ADDR 1000000stake \
                --from <provider-keyname> \
                --keyring-backend test \
                --home /<prov-node-dir> \
                --chain-id provider \
                -y -b block
```
<br/><br/>

__2. Verify the chains validator-set__  
This commands below will print the updated validator consensus info.

```
# Query provider chain valset
interchain-security-pd q tendermint-validator-set --home /<prov-node-dir>
    
# Query provider chain valset    
interchain-security-pd q tendermint-validator-set --home /<cons-node-dir>
```
