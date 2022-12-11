#!/bin/bash
get_final_value() {
    rm -rf ./key-gen

    interchain-security-pd init moniker --home ./key-gen &> /dev/null

    result1=$(interchain-security-pd keys add alice --keyring-backend test --home ./key-gen --output json | jq)
    result2=$(interchain-security-pd keys show alice --keyring-backend test --bech=val --home ./key-gen --output json)

    del_address=$(echo "$result1" | jq -r .address)
    mnemonic=$(echo "$result1" | jq -r .mnemonic)
    valoper=$(echo "$result2" | jq -r .address)
    valcons=$(interchain-security-pd tendermint show-address --home ./key-gen)
    node_key=$(cat ./key-gen/config/node_key.json | jq -c)
    priv_validator_key=$(cat ./key-gen/config/priv_validator_key.json| jq -c)

    echo "validatorID(\"$1\"):  {
            mnemonic:         \"$mnemonic\",
            delAddress:       \"$del_address\",
            valoperAddress:   \"$valoper\",
            valconsAddress:   \"$valcons\",
            privValidatorKey: \`$priv_validator_key\`,
            nodeKey:          \`$node_key\`,
            ipSuffix:         \"$1\",
    },"
}

# call get_final_value function in a loop, incrementing and passing in the ipSuffix value each time
for i in $(seq "$1" "$2");
do
    echo $(get_final_value "$i")
    sleep 0.1
done
    