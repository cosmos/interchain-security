# Interchain Security

**interchain-security** houses the code for implementing Interchain Security: https://blog.cosmos.network/interchain-security-is-coming-to-the-cosmos-hub-f144c45fb035. The repo is currently a WIP and targeting v1 of Interchain Security.

CCV stands for cross chain validation and refers to the subset of Interchain Security related to the staking and slashing communication between the parent and child blockchains. The parent blockchain communicates staking changes to child blockchain(s), while the child blockchain may communicate slashing evidence to the parent blockchain.

The code for CCV is housed under [x/ccv](./x/ccv). The `types` folder contains types and related functions that are used by both parent and child chains, while the `child` module contains the code run by child chains and the `parent` module contains the code run by parent chain.


## Design information

https://github.com/cosmos/gaia/blob/main/docs/interchain-security.md



## Operational Notes

* Hermes set to "all"
* Go-relayer configured on the child port to the parent and on the parent port to the child

Bidirectionally it should look like:

**Parent**
client: 07-tendermint-0
connection: connection-0
channel: channel-0
port: parent

**child**
client: 07-tendermint-0
connection: connection-0
channel: channel-0
port: child


## Imlementation

Split repository into parent and child, with a cmd under each & app.go, etc.

Get binaries named parent and child.  Do it in three windows using iterm2 or similar.  In the first window, start the parent chain-- its config.yml should indicate different ports from the child.  


**parent chain ports**

P2P: 6969
RPC: 6970
GRPC: 6971



**child chain ports**

P2P: 6979
RPC: 6980
GRPC: 6981


