---
sidebar_position: 1
---

# Create an ICS chain with Spawn

## Requirements

- [`go 1.22+`](https://go.dev/doc/install)
- [`Docker`](https://docs.docker.com/get-docker/)

[MacOS + Ubuntu Setup](https://github.com/rollchains/spawn/blob/release/v0.50/docs/versioned_docs/version-v0.50.x/01-setup/01-system-setup.md)

## Getting Started

**Note:** This tutorial focuses on using the Spawn CLI to create an ICS consumer chain. For more complete documentation on Spawn, see the [Spawn documentation](https://rollchains.github.io/spawn/v0.50/).

In this tutorial, we'll create and interact with a new Interchain security enabled blockchain called "consumer", with the token denomination "uconsu".

1. Install Spawn

```shell
# Install from latest source
git clone https://github.com/rollchains/spawn.git --depth 1 --branch v0.50.10

# Change to this directory
cd spawn

# Clear Go modules cache for a fresh install
go clean -modcache

# Install Spawn
make install

# Install Local Interchain (testnet runner)
make get-localic

# Install docker container builder
make get-heighliner

# Verify installations were successful
spawn

local-ic

heighliner

# If you get "command 'spawn' not found", run the following
# Linux / Windows / Some MacOS
echo 'export PATH=$PATH:$(go env GOPATH)/bin' >> ~/.bashrc
source ~/.bashrc

# MacOS
echo 'export PATH=$PATH:$(go env GOPATH)/bin' >> ~/.zshrc
source ~/.zshrc

# Legacy MacOS Go
echo 'export PATH=$PATH:$HOME/go/bin' >> ~/.zshrc
source ~/.zshrc

# Sometimes it can be good to also clear your cache
# especially WSL users
go clean -cache


```

2. Create your chain using the `spawn` command and customize it to your needs!

```shell
GITHUB_USERNAME=<your github username>

spawn new consumer \
--consensus=interchain-security \
--bech32=consu \
--denom=uconsu \
--bin=consumerd \
--disabled=tokenfactory,ibc-packetforward,ibc-ratelimit,cosmwasm,wasm-light-client \
--org=${GITHUB_USERNAME}
```

> _NOTE:_ `spawn` creates a ready to use repository complete with `git` and GitHub CI. It can be quickly pushed to a new repository getting you and your team up and running quickly.

3. Spin up a local testnet for your chain

```shell
cd consumer

# Starts 2 networks for the IBC testnet at http://127.0.0.1:8080.
# - Builds the docker image of your chain
# - Launches a testnet with IBC automatically connected and relayed
#
# Note: you can run a single node, non IBC testnet, with `make sh-testnet`.
make testnet
```

4. Open a new terminal window and send a transaction on your new chain

```shell
# list the keys that have been provisioned with funds in genesis
consumerd keys list

# send a transaction from one account to another
consumerd tx bank send acc0 $(consumerd keys show acc1 -a) 1337uconsu --chain-id=localchain-1

# enter "y" to confirm the transaction
# then query your balances tfor proof the transaction executed successfully
consumerd q bank balances $(consumerd keys show acc1 -a)
```

5. (optional) Send an IBC transaction

```shell
# submit a cross chain transfer from acc0 to the other address
consumerd tx ibc-transfer transfer transfer channel-0 cosmos1hj5fveer5cjtn4wd6wstzugjfdxzl0xpxvjjvr 7uconsu --from=acc0 --chain-id=localchain-1 --yes

# Query the other side to confirm it went through
sleep 10

# Interact with the other chain without having to install the cosmos binary
# - Endpoints found at: GET http://127.0.0.1:8080/info
local-ic interact localcosmos-1 query 'bank balances cosmos1hj5fveer5cjtn4wd6wstzugjfdxzl0xpxvjjvr' --api-endpoint=http://127.0.0.1:8080
```

6. Push your new chain to a github repository

```shell
# Create a new repository on GitHub from the gh cli
gh repo create ics-consumer --source=. --remote=origin --push
```

> You can also push it the old fashioned way with https://github.com/new and `git push origin main`.

In this tutorial, we configured a new custom chain, launched a testnet for it, tested a simple token transfer, and confirmed it was successful.
This tutorial demonstrates just how easy it is to create a brand new custom Cosmos-SDK blockchain from scratch, saving developers time.

## Modify your chain

New module code is usually added in the `x/` directory of your repository.
Check out the [Cosmos SDK documentation](https://docs.cosmos.network/v0.50/build/building-modules/intro) for more information on how to add modules to your chain.

Once you're ready you can preview your chain using the section below.

## List your chain

You can [list your chain on Forge](https://forge.cosmos.network/list-your-chain), even if it's not finished, in the **pre-launch** stage.
