# CHANGELOG

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
