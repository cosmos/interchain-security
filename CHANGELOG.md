# CHANGELOG


## v1.1.0-multiden

Date: May 8th, 2023

**Note:** _This release is consensus breaking for the provider_.

This release combines two fixes that we judged were urgent to get onto the Cosmos Hub before the launch of the first ICS consumer chain.

The first fix is to enable the use of multisigs and Ledger devices when assigning keys for consumer chains. The second is to prevent a possible DOS vector involving the reward distribution system.

### Multisig fix

On April 25th (a week and a half ago), we began receiving reports that validators using multisigs and Ledger devices were getting errors reading `Error: unable to resolve type URL /interchain_security.ccv.provider.v1.MsgAssignConsumerKey: tx parse error when attempting to assign consensus keys for consumer chains`. 

We quickly narrowed the problem down to issues having to do with using the `PubKey` type directly in the `MsgAssignConsumerKey` transaction, and Amino (a deprecated serialization library still used in Ledger devices and multisigs) not being able to handle this. We attempted to fix this with the assistance of the Cosmos-SDK team, but after making no headway for a few days, we decided to simply use a JSON representation of the `PubKey` in the transaction. This is how it is usually represented anyway. We have verified that this fixes the problem.

### Distribution fix

The ICS distribution system works by allowing consumer chains to send rewards to a module address on the provider called the `FeePoolAddress`. From here they are automatically distributed to all validators and delegators through the distribution system that already exists to distribute staking rewards. The `FeePoolAddress` is usually blocked so that no tokens can be sent to it, but to enable ICS distribution we had to unblock it.

We recently realized that unblocking the `FeePoolAddress` could enable an attacker to send a huge number of different denoms into the distribution system. The distribution system would then attempt to distribute them all, leading to out of memory errors. Fixing a similar attack vector that existed in the distribution system before ICS led us to this realization.

To fix this problem, we have re-blocked the `FeePoolAddress` and created a new address called the `ConsumerRewardsPool`. Consumer chains now send rewards to this new address. There is also a new transaction type called `RegisterConsumerRewardDenom`. This transaction allows people to register denoms to be used as rewards from consumer chains. It costs 10 Atoms to run this transaction.The Atoms are transferred to the community pool. Only denoms registered with this command are then transferred to the `FeePoolAddress` and distributed out to delegators and validators.

## v1.1.0

Date: March 24th, 2023

This is a minor release of Interchain Security (ICS), also known as _Replicated Security_ (RS), which resolves a bug in the core protocol.

Changes included:

* [fix StopConsumerChain not running in cachedContext](https://github.com/cosmos/interchain-security/pull/802)

## v1.0.0

Date: February 6th, 2023

This is the first version of Interchain Security (ICS), also known as _Replicated Security_ (RS). 
Replicated Security is a feature which will allow a chain -- referred to as the _provider_ -- to share security with other chains -- referred to as _consumers_. 
This means that the provider's validator set will be granted the right to validate consumer chains.
The communication between the provider and the consumer chains is done through the IBC protocol over a unique, ordered channel (one for each consumer chain). Thus, RS is an IBC application.

### Features / sub-protocols

RS consist of the following core features:

- **Channel Initialization**: Enables the provider to add new consumer chains. This process is governance-gated, i.e., to add a new consumer chain, a `ConsumerAdditionProposal` governance proposal must be sent to the provider and it must receive the necessary votes.
- **Validator Set Update**: Enables the provider to 
  (1) update the consumers on the voting power granted to validators (based on the changes in the active validator set on the provider chain), 
  and (2) ensure the timely completion of unbonding operations (e.g., undelegations).
- **Consumer Initiated Slashing**: Enables the provider to jail validators for downtime infractions on the consumer chains. 
- **Reward Distribution**: Enables the consumers to transfer to the provider (over IBC) a portion of their block rewards as payment for the security provided. Once transferred, these rewards are distributed on the provider using the protocol in the [distribution module of Cosmos SDK](https://docs.cosmos.network/v0.45/modules/distribution/). 
- **Consumer Chain Removal**: Enables the provider to remove a consumer either after a `ConsumerRemovalProposal` passes governance or after one of the timeout periods elapses -- `InitTimeoutPeriod`, `VscTimeoutPeriod`, `IBCTimeoutPeriod`.
- **Social Slashing**: Equivocation offenses (double signing etc.) on consumer chains are logged, and then can be used in a governance proposal to slash the validators responsible.

In addition, RS has the following features:

- **Key Assignment**: Enables validator operators to use different consensus keys for each consumer chain validator node that they operate.
- **Jail Throttling**: Enables the provider to slow down a "worst case scenario" attack where a malicious consumer binary attempts to jail a significant amount (> 2/3) of the voting power, effectively taking control of the provider.

### Dependencies

- [ibc-go](https://github.com/cosmos/ibc-go): [v4.2.0](https://github.com/cosmos/ibc-go/blob/release/v4.2.x/CHANGELOG.md)
- [cosmos-sdk](https://github.com/cosmos/cosmos-sdk): [v0.45.12-ics](https://github.com/cosmos/cosmos-sdk/tree/v0.45.13-ics)
- [tendermint](https://github.com/informalsystems/tendermint): [0.34.24](https://github.com/informalsystems/tendermint/tree/v0.34.24)
