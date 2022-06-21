# Roadmap Interchain Security

_Lastest update: June 20th, 2022_

This document endeavors to inform the wider Cosmos community about plans and priorities for the work on Interchain Security (ICS). This roadmap should be read as a high-level guide, rather than a commitment to schedules and deliverables. The degree of specificity is inversely proportional to the timeline. We will update this document periodically to reflect the status and plans.
 
## Q2 - 2022

- Finalize core ICS features that enable a provider chain to provide security to multiple consumer chains.
  - https://github.com/cosmos/interchain-security/issues/35
  - https://github.com/cosmos/interchain-security/issues/27
  - https://github.com/cosmos/interchain-security/issues/39
- Create a minimum viable consumer chain (MVCC) that enables testing core ICS features.
  - https://github.com/cosmos/interchain-security/issues/139
- Create in-memory test driver based on the ibc-go testing framework.
  - https://github.com/cosmos/interchain-security/pull/126
- Finalize ICS spec
  - https://github.com/cosmos/ibc/issues/670

## Q3 - 2022

- Differential testing of ICS that tests the core ICS features (excluding distribution, channel initialization, consumer chain removal, expired clients).
  - https://github.com/cosmos/interchain-security/issues/137
- Create a governance-enabled consumer chain that enables a native token to be staked for governance. 
  - https://github.com/cosmos/interchain-security/issues/141
  - https://github.com/cosmos/interchain-security/issues/82
- Create a CosmWasm-enabled consumer chain.
  - https://github.com/cosmos/interchain-security/issues/143
- Enable validators to set different consensus keys for different consumer chains.
  - https://github.com/cosmos/interchain-security/issues/26
- Enable the chains to be easily restarted in case they halt.
  - https://github.com/cosmos/interchain-security/issues/158
  - https://github.com/cosmos/interchain-security/issues/156
  - https://github.com/cosmos/interchain-security/issues/125
  - https://github.com/cosmos/interchain-security/issues/121
- Fix remaining issues
  - https://github.com/cosmos/interchain-security/issues
- Test edge cases regarding channel initialization, consumer chain removal, and clients expiring.
- Upgrade to SDK v0.46
  - https://github.com/cosmos/interchain-security/issues/63
- Integrate with Liquid Staking module
  - https://github.com/cosmos/interchain-security/issues/67
- Integrate with Cosmos Hub (Gaia)
  - https://github.com/cosmos/interchain-security/issues/131
- Incentivized testnet 
- External audit
- Integration test 
