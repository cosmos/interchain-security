start testnet: go run ./integration-tests/...

check provider: interchain-securityd query tendermint-validator-set --home /provider --chain-id provider --node http://7.7.7.1:26658

check consumer: interchain-securityd query tendermint-validator-set --home /consumer --chain-id consumer --node http://7.7.8.2:26658

add key if neccesary: 

[root@44d7b70b1c13 /]# interchain-securityd keys add jehan --home /provider --recover
> Enter your bip39 mnemonic
sight similar better jar bitter laptop solve fashion father jelly scissors chest uniform play unhappy convince silly clump another conduct behave reunion marble animal

delegate some coins: interchain-securityd tx staking delegate cosmosvaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qakmjnw 1000000stake --from jehan --home /provider --chain-id provider --node http://7.7.7.1:26658 -b block

check provider: interchain-securityd query tendermint-validator-set --home /provider --chain-id provider --node http://7.7.7.1:26658

check consumer: interchain-securityd query tendermint-validator-set --home /consumer --chain-id consumer --node http://7.7.8.2:26658

relay packets: /root/.cargo/bin/hermes clear packets provider parent channel-0

check consumer: interchain-securityd query tendermint-validator-set --home /consumer --chain-id consumer --node http://7.7.8.2:26658