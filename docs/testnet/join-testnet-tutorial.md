## Join the Interchain-Security Testnet
This guide contains the instructions for joining a Interchain-Security Testnet. You can find the instructions to setup a IS-testnet from scratch [here](https://github.com/sainoe/IS-testnet/blob/main/is-testnet-tutorial.md). 

---

### Prerequesites
- Go 1.18+
- Interchain-Security binaries
- jq

#### Install Go

```
curl -OL https://golang.org/dl/go1.18.4.linux-amd64.tar.gz

sudo tar -C /usr/local -xvf go1.18.4.linux-amd64.tar.gz

export PATH=$PATH:/usr/local/go/bin

export PATH=$PATH:$(go env GOPATH)/bin
```

---

#### Install Interchain-Security binaries

```
git clone https://github.com/cosmos/interchain-security.git

cd interchain-security

make install
```

---

#### Install jq
```
#Linux
apt-get install jq

# OSX
brew install jq
```

---

### Run a validator on the Provider chain
This section will explain you how to setup and run an node in order to participate to the Provider chain as a validator.
Choose a directory name `<prov-node-dir>` (e.g. `~/provider`) to store the provider chain node files. Along this guide,
the provider and consumer chain ids used are respectively `provider` and `consumer`.

* *If you have completed the [IS-tesnet tutorial](https://github.com/sainoe/IS-testnet/blob/main/is-testnet-tutorial.md) on the same machine,
  be sure to use <b>a different node folder</b>!*

__1. Remove any existing directory__  

`rm -rf <prov-node-dir>`  
 <br/><br/>  

__2. Create the node directory__  
This command generates the required node directory stucture along with the intial genesis file.
```
interchain-security-pd init <prov-node-moniker> --chain-id provider --home <prov-node-dir>
```
<br/><br/>

__3. Generate the node keypair__  
To generate the node account keypair use the following command.
```
interchain-security-pd keys add <provider-keyname> --home <prov-node-dir> --keyring-backend test --output json > <prov-node-dir>/<provider_keyname_keypair>.json 2>&1
```  

* *The `--keyring-backend` option can be removed if you would prefer securing the account with a password*
<br/><br/>

__4. Get the Provider chain genesis file__
Import the provider chain genesis file from the IS-Testnet you want to join. 
For instance, by downloading it from pastbin using curl like the command below. 

```
curl -o <prov-node-dir>/config/genesis.json https://pastebin.com/<your-pastbin-genesis-dump>
```  

<br/><br/>


__5. Run the node__  
This command will run the node using the coordinator persistent peer address retrieved from the genesis state. Replace the `<prov-node-dir>` with your your chosen provider node directory.  
```
# Retrieve public ip address
MY_IP=$(host -4 myip.opendns.com resolver1.opendns.com | grep "address" | awk '{print $4}')

# Get persistent peer
COORDINATOR_P2P_ADDRESS=$(jq -r '.app_state.genutil.gen_txs[0].body.memo' <prov-node-dir>/config/genesis.json)

# Run node
interchain-security-pd start --home <prov-node-dir> \
        --rpc.laddr tcp://${MY_IP}:26658 \
        --grpc.address ${MY_IP}:9091 \
        --address tcp://${MY_IP}:26655 \
        --p2p.laddr tcp://${MY_IP}:26656 \
        --grpc-web.enable=false \
        --p2p.persistent_peers $COORDINATOR_P2P_ADDRESS \
        &> <prov-node-dir>/logs &
```
   
   
* *If you get the error "can't bind address xxx.xxx.x.x", try using `127.0.0.1` instead.*   


* *If you're running the coordinator node on the same local machine, you might
need to change its IP address to 127.0.0.1.*   


<br/><br/>

__6. Fund your account__   
Make sure your node account has at least `1000000stake` coins in order to stake.
Verify your account balance using the command below.
```
# Setup the client RPC endpoint using the following command.
sed -i -r "/node =/ s/= .*/= \"tcp:\/\/${MY_IP}:26658\"/" <prov-node-dir>/config/client.toml

# Check your account balance
interchain-security-pd q bank balances $(jq -r .address <prov-node-dir>/<provider-keyname_keypair>.json) --home <prov-node-dir>
```

* *Ask to get your local account fauceted or use the command below if you have access to another account at least extra `1000000stake` tokens.*

 ```
# Get local account addresses
ACCOUNT_ADDR=$(interchain-security-pd keys show <your-keyname> \
       --keyring-backend test --home <prov-node-dir> --output json | jq -r '.address')

# Run this command 
interchain-security-pd tx bank send <source-address> <destination-address> \
        1000000stake --from <source-keyname> --keyring-backend test --home <prov-node-dir> --chain-id provider -b block 
```

<br/><br/>
  
__7. Bond the validator__  
Bond your local node as a validator by sending the following transaction.

```
# Get the validator node pubkey 
VAL_PUBKEY=$(interchain-security-pd tendermint show-validator --home <prov-node-dir>)

# Create the validator
interchain-security-pd tx staking create-validator \
            --amount 1000000stake \
            --pubkey $VAL_PUBKEY \
            --from <provider-keyname> \
            --keyring-backend test \
            --home <prov-node-dir> \
            --chain-id provider \
            --commission-max-change-rate 0.01 \
            --commission-max-rate 0.2 \
            --commission-rate 0.1 \
            --moniker <prov-node-moniker> \
            --min-self-delegation 1 \
            -b block -y
```
<br>
Verify that your validator node is now part of the validator-set.

```
interchain-security-pd q tendermint-validator-set --home <prov-node-dir>
```  

---

### Run a validator on the Consumer chain
The following steps will explain you how to configure and run a validator node for joining the Consumer chain.  

__1. Remove any existing directory__  

```
rm -rf <cons-node-dir>
```
<br/><br/>

__2. Create the node directory__  

This command generates the required node directory stucture along with the intial genesis file.
```
interchain-security-cd init <cons-node-moniker> --chain-id consumer --home <cons-node-dir>
```
<br/><br/>

__3. Generate a node keypair__   

This command create a keypair for the consumer node.
```
interchain-security-cd keys add <consumer-keyname> \
    --home <cons-node-dir> --output json > <cons-node-dir>/<consumer_keyname_keypair>.json 2>&1
```
<br/><br/>

__4. Import Consumer chain genesis file__  

Import the consumer genesis file to your local node folder as explained in the provider chain section point 5 .
<br/><br/>

__5. Import validator keypair node__  
 
The following will copy the required validator keypair files in order to run the same node on the consumer chain.  

```
cp <prov-node-dir>/config/node_key.json <cons-node-dir>/config/node_key.json

cp <prov-node-dir>/config/priv_validator_key.json <cons-node-dir>/config/priv_validator_key.json
```
<br/><br/>

__6. Run the validator node__  

This command will run the validator on the consumer chain.  

```
# Get persistent peer address
COORDINATOR_P2P_ADDRESS=$(jq -r '.app_state.genutil.gen_txs[0].body.memo' <prov-node-dir>/config/genesis.json)

# Get consumer chain coordinator node p2p address
CONSUMER_P2P_ADDRESS=$(echo $COORDINATOR_P2P_ADDRESS | sed 's/:.*/:26646/')

interchain-security-cd start --home <cons-node-dir> \
        --rpc.laddr tcp://${MY_IP}:26648 \
        --grpc.address ${MY_IP}:9081 \
        --address tcp://${MY_IP}:26645 \
        --p2p.laddr tcp://${MY_IP}:26646 \
        --grpc-web.enable=false \
        --p2p.persistent_peers $CONSUMER_P2P_ADDRESS \
        &> <cons-node-dir>/logs &
```
<br/><br/>

__7. Query the consumer chain node__  

Update the node client RPC endpoint using the following command.  

```
sed -i -r "/node =/ s/= .*/= \"tcp:\/\/${MY_IP}:26648\"/" <cons-node-dir>/config/client.toml
```

Query the consumer chain and check that the validator node was added to the validator set.

```
interchain-security-cd q tendermint-validator-set --home <cons-node-dir>
```

---


### Test the CCV protocol
These optional steps show you how CCV updates the Consumer chain validator-set voting power. In order to do so, we will delegate some tokens to the validator on the Provider chain and verify that the Consumer chain validator-set gets updated.

__1. Delegate tokens__  
```
# Get validator delegations
DELEGATIONS=$(interchain-security-pd q staking delegations \
    $(jq -r .address <provider-keyname>_keypair.json) --home <prov-node-dir> -o json)

# Get validator operator address
OPERATOR_ADDR=$(echo $DELEGATIONS | jq -r '.delegation_responses[0].delegation.validator_address')


# Delegate tokens
interchain-security-pd tx staking delegate $OPERATOR_ADDR 1000000stake \
                --from <provider-keyname> \
                --keyring-backend test \
                --home <prov-node-dir> \
                --chain-id provider \
                -y -b block
```

__2.Check the validator-set__  
This commands below will print the updated validator consensus info.

```
# Get validator consensus address
VAL_ADDR=$(interchain-security-pd tendermint show-address --home <prov-node-dir>)
        
# Query validator consenus info        
interchain-security-cd q tendermint-validator-set --home <cons-node-dir> | grep -A11 $VAL_ADDR
```





