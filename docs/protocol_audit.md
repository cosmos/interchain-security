# Interchain Security: Protocol Audit

This document contains information on the protocol audit performed by the Apalache team from Informal Systems. 

For a general overview of the quality assurance process necessary for the release of Interchain Security v1, take a look at [docs/quality_assurance.md](./quality_assurance.md). 

## Reading / onboarding materials

- Interchain Security [specification](https://github.com/cosmos/ibc/blob/marius/ccv/spec/app/ics-028-cross-chain-validation/README.md)
- Quality Assurance [overview](./quality_assurance.md)

## Plan

Priority of concerns:
1. The correctness (safety and liveness) of the provider chain (for multiple consumer chains), see [QA overview](./quality_assurance.md#provider-chain-correctness).
2. The correctness (safety and liveness) of the Interchain Security protocol, see [QA overview](./quality_assurance.md#interchain-security-protocol-correctness).

Sub-protocols to focus on:
- [Channel Initialization](https://github.com/cosmos/ibc/blob/marius/ccv/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#channel-initialization)

- [Validator Set Update](https://github.com/cosmos/ibc/blob/marius/ccv/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#validator-set-update) with a focus on [Completion of Unbonding Operations](https://github.com/cosmos/ibc/blob/marius/ccv/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#completion-of-unbonding-operations) (**good starting point**)
  
- [Consumer Initiated Slashing](https://github.com/cosmos/ibc/blob/marius/ccv/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#consumer-initiated-slashing)




