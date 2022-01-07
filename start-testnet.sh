#! /bin/bash

starport chain serve -r --home ./testnet/artifacts/consumer --config ./config-consumer.yml &

starport chain serve -r --home ./testnet/artifacts/provider --config ./config-provider.yml