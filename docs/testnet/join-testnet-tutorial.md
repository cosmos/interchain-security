## Join the Interchain-Security Testnet
This guide contains the instructions for joining a Interchain-Security Testnet. You can find the instructions to setup a IS-testnet from scratch [here](./start-testnet-tutorial.md). 

---

### Prerequesites
- Go 1.18+ <sub><sup>([installation notes](https://go.dev/doc/install))<sub><sup>
- Interchain Security binaries <sub><sup>([installation notes](./start-testnet-tutorial.md#install-the-interchain-security-binary))<sub><sup>
- Rust 1.60+ <sub><sup>([installation notes](https://www.rust-lang.org/tools/install))<sub><sup>
- Hermes v1.0.0-rc.0 <sub><sup>([installation notes](https://hermes.informal.systems/getting_started.html))<sub><sup>
- jq  <sub><sup>([installation notes](https://stedolan.github.io/jq/download/))<sub><sup>


---

### Run a validator on the Provider chain
This section will explain you how to setup and run an node in order to participate to the Provider chain as a validator.
Choose a directory name (e.g. `~/provider-recruit`) to store the provider chain node files.

* *If you have completed the [IS-testnet tutorial](./start-testnet-tutorial.md) on the same machine,
  be sure to use <b>a different node folder</b>!*

__1. Remove any existing directory__  

```
PROV-NODE-DIR="~/provider-recruit"
rm -rf $PROV-NODE-DIR
```  
 <br/><br/>  

__2. Create the node directory__  
The command below initializes the node's configuration files. The `$PROV-NODE-MONIKER` argument is a public moniker that will identify your validator, i.e. `coop-validator`).Additionally, in this guide its assumed that the provider and consumer chains id are self-titled.
```
PROV-NODE-MONIKER=coop-validator
PROV-CHAIN-ID=provider

interchain-security-pd init $PROV-NODE-MONIKER --chain-id $PROV-CHAIN-ID --home $PROV-NODE-DIR
```
<br/><br/>

__3. Generate the node keypair__  
This following step creates a public/private keypair and stores it under the given keyname of your choice. The output is also exported into a json file for later use.

```
$PROV-KEY=provider-key

interchain-security-pd keys add $PROV-KEY --home $PROV-NODE-DIR --keyring-backend test --output json > ${PROV-NODE-DIR}/${PROV-KEY}.json 2>&1
```  

* *The `--keyring-backend` option can be removed if you would prefer securing the account with a password*
<br/><br/>

__4. Get the Provider chain genesis file__
Import the provider chain genesis file from the IS-Testnet you want to join. You can either ask to the testnet coordinator or
, if you have completed the IS-testnet tutorial, you can copy the genesis file using the following command: 

```
$PROV-COORDINATOR-DIR="~/provider"
cp ${PROV-COORDINATOR-DIR}/config/genesis.json ${PROV-COORDINATOR-DIR}/config/genesis.json
```  

<br/><br/>


__5. Run the node__  
This command will run the node using the coordinator persistent peer address retrieved from the genesis state.
```
# Retrieve public ip address
MY_IP=$(host -4 myip.opendns.com resolver1.opendns.com | grep "address" | awk '{print $4}')

# Get persistent peer
COORDINATOR_P2P_ADDRESS=$(jq -r '.app_state.genutil.gen_txs[0].body.memo' ${PROV-NODE-DIR}/config/genesis.json)

# Run node
interchain-security-pd start --home $PROV-NODE-DIR \
        --rpc.laddr tcp://${MY_IP}:26658 \
        --grpc.address ${MY_IP}:9091 \
        --address tcp://${MY_IP}:26655 \
        --p2p.laddr tcp://${MY_IP}:26656 \
        --grpc-web.enable=false \
        --p2p.persistent_peers $COORDINATOR_P2P_ADDRESS \
        &> ${PROV-NODE-DIR}/logs &
```
   
   
* *If you get the error "can't bind address xxx.xxx.x.x", try using `127.0.0.1` instead.*   


* *If you're running the coordinator node on the same local machine, you might
need to change its IP address to 127.0.0.1.*   


<br/><br/>

__6. Setup client RPC endpoint__  
This command changes the default RPC client endpoint port of our node. It is exposed by Tendermint and allows us to query the chains' states and to submit transactions.This command below change the client RPC endpoint using the following command.

sed -i -r "/node =/ s/= .*/= \"tcp:\/\/${MY_IP}:26658\"/" ${PROV-NODE-DIR}/config/client.toml


<br/><br/>


__7. Fund your account__   
Make sure your node account has at least `1000000stake` coins in order to stake.
Verify your account balance using the command below.
```

# Check your account balance
interchain-security-pd q bank balances $(jq -r .address ${PROV-NODE-DIR}/${PROV-KEY}.json) --home $PROV-NODE-DIR
```

* *Ask to get your local account fauceted or use the command below if you have access to another account at least extra `1000000stake` tokens.*

 ```
# Get local account addresses
ACCOUNT_ADDR=$(interchain-security-pd keys show $PROV-KEY \
       --keyring-backend test --home $PROV-NODE-DIR --output json | jq -r '.address')

# Run this command 
interchain-security-pd tx bank send <source-address> <destination-address> \
        1000000stake --from <source-keyname> --keyring-backend test --home $PROV-NODE-DIR --chain-id provider -b block 
```

<br/><br/>

### Run a validator on the Consumer chain
The following steps will explain you how to configure and run a validator node for joining the Consumer chain.  

__1. Remove any existing directory__  

```
CONS-NODE-DIR="~/consumer"
rm -rf $CONS-NODE-DIR
```
<br/><br/>

__2. Create the node directory__  

This command generates the required node directory stucture along with the intial genesis file.  

```
CONS-NODE-MONIKER=consumer-node-moniker
CONS-CHAIN-ID=consumer

interchain-security-cd init $CONS-NODE-MONIKER --chain-id $CONS-CHAIN-ID --home $CONS-NODE-DIR
```

<br/><br/>

__3. Generate a node keypair__   

This command create a keypair for the consumer node.
```
$CONS-KEY=consumer-key

interchain-security-cd keys add $CONS-KEY \
    --home $CONS-NODE-DIR --output json > ${CONS-NODE-DIR}/${CONS-KEY}.json 2>&1
```
<br/><br/>

__4. Import Consumer chain genesis file__  

Import the consumer genesis file to your local node folder as explained in the [provider chain section](#4-get-the-provider chain-genesis-file).

<br/><br/>

__5. Import validator keypair node__  
 
The following will copy the required validator keypair files in order to run the same node on the consumer chain.  

```
cp ${PROV-NODE-DIR}/config/node_key.json ${CONS-NODE-DIR}/config/node_key.json

cp ${PROV-NODE-DIR}/config/priv_validator_key.json ${CONS-NODE-DIR}/config/priv_validator_key.json
```
<br/><br/>

__6. Setup client RPC endpoint__  
This command updates the consumer node RPC client config and allow to query the chain states as explained in the above.  
  
`sed -i -r "/node =/ s/= .*/= \"tcp:\/\/localhost:26648\"/" ${CONS-NODE-DIR}/config/client.toml`
<br/><br/>

__7. Run the validator node__  

This command will run the validator on the consumer chain.  

```
# Get persistent peer address
COORDINATOR_P2P_ADDRESS=$(jq -r '.app_state.genutil.gen_txs[0].body.memo' ${PROV-NODE-DIR}/config/genesis.json)

# Get consumer chain coordinator node p2p address
CONSUMER_P2P_ADDRESS=$(echo $COORDINATOR_P2P_ADDRESS | sed 's/:.*/:26646/')

interchain-security-cd start --home $CONS-NODE-DIR \
        --rpc.laddr tcp://${MY_IP}:26648 \
        --grpc.address ${MY_IP}:9081 \
        --address tcp://${MY_IP}:26645 \
        --p2p.laddr tcp://${MY_IP}:26646 \
        --grpc-web.enable=false \
        --p2p.persistent_peers $CONSUMER_P2P_ADDRESS \
        &> ${CONS-NODE-DIR}logs &
```

<br/><br/>


__8. Bond the validator__  
Now that both consumer and provider nodes are running, we can bond it to be a validator on boths chain, by submitting the following transaction to the provider chain.

```
# Get the validator node pubkey 
VAL-PUBKEY=$(interchain-security-pd tendermint show-validator --home $PROV-NODE-DIR)

# Create the validator
interchain-security-pd tx staking create-validator \
            --amount 1000000stake \
            --pubkey $VAL-PUBKEY \
            --from $PROV-KEY \
            --keyring-backend test \
            --home $PROV-NODE-DIR \
            --chain-id provider \
            --commission-max-change-rate 0.01 \
            --commission-max-rate 0.2 \
            --commission-rate 0.1 \
            --moniker $PROV-MONIKER \
            --min-self-delegation 1 \
            -b block -y
```
<br>
Verify that your validator node is now part of the validator-set.

```
interchain-security-pd q tendermint-validator-set --home $PROV-NODE-DIR

interchain-security-pd q tendermint-validator-set --home $PROV-NODE-DIR
```  

---


### Test the CCV protocol
These optional steps show you how CCV updates the Consumer chain validator-set voting power. In order to do so, we will delegate some tokens to the validator on the Provider chain and verify that the Consumer chain validator-set gets updated.

__1. Delegate tokens__  
```
# Get validator delegations
DELEGATIONS=$(interchain-security-pd q staking delegations \
    $(jq -r .address ${PROV-KEY}.json) --home $PROV-NODE-DIR -o json)

# Get validator operator address
OPERATOR-ADDR=$(echo $DELEGATIONS | jq -r '.delegation_responses[0].delegation.validator_address')


# Delegate tokens
interchain-security-pd tx staking delegate $OPERATOR-ADDR 1000000stake \
                --from ${PROV-KEY} \
                --keyring-backend test \
                --home $PROV-NODE-DIR \
                --chain-id $PROV-CHAIN-ID \
                -y -b block
```

<br/><br/>

__2.Check the validator set__  
This commands below will print the updated validator set.

```
# Get validator consensus address
VAL-ADDR=$(interchain-security-pd tendermint show-address --home $PROV-NODE-DIR)
        
# Query validator consenus info        
interchain-security-cd q tendermint-validator-set --home $CONS-NODE-DIR | grep -A11 $VAL-ADDR
```
