# Interchain Security

**interchain-security** houses the code for implementing Interchain Security: https://blog.cosmos.network/interchain-security-is-coming-to-the-cosmos-hub-f144c45fb035. The repo is currently a WIP and targetting v1 of Interchain Security.

CCV stands for cross chain validation and refers to the subset of Interchain Security related to the staking and slashing communication between the provider and consumer blockchains. The provider blockchain communicates staking changes to consumer blockchain(s), while the consumer blockchain may communicate slashing evidence to the provider blockchain.

The code for CCV is housed under [x/ccv](./x/ccv). The `types` folder contains types and related functions that are used by both provider and consumer chains, while the `consumer` module contains the code run by consumer chains and the `provider` module contains the code run by provider chain.

NOTE: At the moment the testing app may not be functional, please rely on the IBC testing suite to write unit tests for the moment.

## Get started

```
starport chain serve
```

`serve` command installs dependencies, builds, initializes, and starts a testing blockchain in development.

### Configure

The testing blockchain in development can be configured with `config.yml`. To learn more, see the [Starport docs](https://docs.starport.network).

### Launch

To launch a testing blockchain live on multiple nodes, use `starport network` commands. Learn more about [Starport Network](https://github.com/tendermint/spn).

### Web Frontend

Starport has scaffolded a Vue.js-based web app in the `vue` directory. Run the following commands to install dependencies and start the app:

```
cd vue
npm install
npm run serve
```

The frontend app is built using the `@starport/vue` and `@starport/vuex` packages. For details, see the [monorepo for Starport front-end development](https://github.com/tendermint/vue).

## Release
To release a new version of your blockchain, create and push a new tag with `v` prefix. A new draft release with the configured targets will be created.

```
git tag v0.1
git push origin v0.1
```

After a draft release is created, make your final changes from the release page and publish it.

### Install
To install the latest version of your blockchain node's binary, execute the following command on your machine:

```
curl https://get.starport.network/cosmos/interchain-security@latest! | sudo bash
```
`cosmos/interchain-security` should match the `username` and `repo_name` of the Github repository to which the source code was pushed. Learn more about [the install process](https://github.com/allinbits/starport-installer).

## Learn more

- [IBC Docs](https://docs.cosmos.network/master/ibc/)
- [IBC Protocol](https://ibcprotocol.org/)
- [IBC Specs](https://github.com/cosmos/ibc)
- [Starport](https://github.com/tendermint/starport)
- [Starport Docs](https://docs.starport.network)
- [Cosmos SDK documentation](https://docs.cosmos.network)
- [Cosmos SDK Tutorials](https://tutorials.cosmos.network)
- [Discord](https://discord.gg/cosmosnetwork)
