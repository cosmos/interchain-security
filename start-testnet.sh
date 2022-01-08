#! /bin/bash

killport () {
    lsof -i ":$1" | awk 'NR > 1 {print $2}' | xargs kill
}

killport 26661
killport 26660
killport 6062
killport 9092
killport 9093
killport 1319
killport 4501

killport 26659
killport 26658
killport 6061
killport 9090
killport 9091
killport 1318
killport 4500


starport chain serve -r --home ./testnet/artifacts/consumer --config ./config-consumer.yml &

starport chain serve -r --home ./testnet/artifacts/provider --config ./config-provider.yml &

starport relayer configure --advanced \
--source-rpc "http://0.0.0.0:26659" \
--source-faucet "http://0.0.0.0:4500" \
--source-account "default" \
--source-port "blog" \
--source-version "blog-1" \
--source-gasprice "0.00025stake" \
--source-gaslimit 300000 \
--source-prefix "cosmos" \
--target-rpc "http://0.0.0.0:26661" \
--target-faucet "http://0.0.0.0:4501" \
--target-account "default" \
--target-port "blog" \
--target-version "blog-1" \
--target-gasprice "0.00025stake" \
--target-gaslimit 300000 \
--target-prefix "cosmos" \
