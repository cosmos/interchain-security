# Interchain Security Parameters

The parameters necessary for Interchain Security (ICS) are defined in 

- the `Params` structure in `proto/interchain_security/ccv/provider/v1/provider.proto` for the provider;
- the `Params` structure in `proto/interchain_security/ccv/consumer/v1/consumer.proto` for the consumer.

## Time-based parameters

ICS relies on the following time-based parameters.

- `UnbondingTime` is defined in the `x/staking` module of the cosmos-sdk, i.e., see [protobuf](https://github.com/cosmos/cosmos-sdk/blob/9c145c827001222df2e3e1101010874aeac20997/proto/cosmos/staking/v1beta1/staking.proto#L294). This is the unbonding period on the provider chain. 
  For clarity, we denote the unbonding periods on the provider by `ProviderUnbondingPeriod`
- `UnbondingPeriod` is defined in `consumer.proto` and it is the unbonding period on the consumer chain. For clarity, we denote the unbonding periods on the consumer by `ConsumerUnbondingPeriod`. 
  The `ConsumerUnbondingPeriod` is set via the `ConsumerAdditionProposal` gov proposal to add a new consumer chain. 
  Unbonding operations (such as undelegations) MUST wait for the unbonding period on every consumer to elapse. Therefore, for an improved user experience, the `ConsumerAdditionProposal` on every consumer chain SHOULD be smaller than `ProviderUnbondingPeriod`, i.e., 
  ```
  ConsumerUnbondingPeriod = ProviderUnbondingPeriod - one day
  ```
- `TrustingPeriodFraction` is used to calculate the `TrustingPeriod` of created IBC clients on both provider and consumer chains.  
  For example, a `TrustingPeriodFraction` of `0.5` would entail that the `TrustingPeriod` of clients to the provider will be `ProviderUnbondingPeriod / 2`, while the `TrustingPeriod` of clients to every consumer will be `ConsumerUnbondingPeriod / 2`.
  Note that a client MUST be update within the `TrustingPeriod` in order to remain active. 
  For more details, see the [IBC specification of Tendermint clients](https://github.com/cosmos/ibc/blob/main/spec/client/ics-007-tendermint-client/README.md).
- `CCVTimeoutPeriod` is the period used to compute the timeout timestamp when sending IBC packets. 
  For more details, see the [IBC specification of Channel & Packet Semantics](https://github.com/cosmos/ibc/blob/main/spec/core/ics-004-channel-and-packet-semantics/README.md#sending-packets).
  `CCVTimeoutPeriod` may have different values on the provider and consumer chains. If a sent packet is not relayed within this period, then the packet times out, the CCV channel is closed, and the corresponding consumer removed.
  The `CCVTimeoutPeriod` on the provider MUST be larger than `ConsumerUnbondingPeriod`. 
  The `CCVTimeoutPeriod` on the consumer is initial set via the `ConsumerAdditionProposal` gov proposal to add the consumer. 
- `InitTimeoutPeriod` is the maximum time duration the Channel Initialization subprotocol may execute, 
  i.e., for any consumer chain, if the CCV channel is not established within `InitTimeoutPeriod` since the `ConsumerAdditionProposal` was handled (the client to the consumer was created), then the consumer chain is removed.
- `VscTimeoutPeriod` is the maximum time duration between sending any `VSCPacket` to any consumer chain and receiving the corresponding `VSCMaturedPacket`, without timing out the consumer chain and consequently removing it.
  `VscTimeoutPeriod` MUST be larger than the `ConsumerUnbondingPeriod`.
- `BlocksPerDistributionTransmission` is the number of blocks between rewards transfers from the consumer to the provider. 
- `TransferPeriodTimeout` is the period used to compute the timeout timestamp when sending IBC transfer packets from a consumer to the provider. If this timeout expires, then the transfer is attempted again after `BlocksPerDistributionTransmission` blocks. 
  The `TransferPeriodTimeout` on the consumer is initial set via the `ConsumerAdditionProposal` gov proposal to add the consumer. 
  The `TransferPeriodTimeout` SHOULD be smaller than `BlocksPerDistributionTransmission x avg_block_time`, to make it easier to reason about the distribution subprotocol.   
- `SlashMeterReplenishPeriod` exists on the provider such that once the slash meter becomes not-full, the slash meter is replenished after this period has elapsed. The meter is replenished to an amount equal to the slash meter allowance for that block, or `SlashMeterReplenishFraction * CurrentTotalVotingPower`.
- `SlashMeterReplenishFraction` exists on the provider as the portion (in range [0, 1]) of total voting power that is replenished to the slash meter when a replenishment occurs. This param also serves as a maximum fraction of total voting power that the slash meter can hold.
- `MaxThrottledPackets` exists on the provider as the maximum amount of throttled slash or vsc matured packets that can be queued from a single consumer before the provider chain halts, it should be set to a large value. This param would allow provider binaries to panic deterministically in the event that packet throttling results in a large amount of state-bloat. In such a scenario, packet throttling could prevent a violation of safety, at the cost of liveness.
