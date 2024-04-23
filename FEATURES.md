# Features

The following table indicates the major ICS features available in the [currently active releases](./RELEASES.md#version-matrix):

| Feature | `v3.2.0` | `v3.3.0` | `v3.3.3-lsm` | `v4.0.0` | `v4.1.1` | `v4.1.1-lsm` | 
|---------|---------:|---------:|-------------:|---------:|---------:|-------------:|
| [Channel initialization: new chains](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#channel-initialization-new-chains) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Validator set update](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#validator-set-update) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Completion of unbonding operations](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#completion-of-unbonding-operations) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Consumer initiated slashing](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#consumer-initiated-slashing) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Reward distribution](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#reward-distribution) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Consumer chain removal](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#consumer-chain-removal) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Key assignment](https://github.com/cosmos/interchain-security/issues/26) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Jail throttling](https://github.com/cosmos/interchain-security/issues/404) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Soft opt-out](https://github.com/cosmos/interchain-security/issues/851)  | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Channel initialization: existing chains](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#channel-initialization-existing-chains) (aka [Standalone to consumer changeover](https://github.com/cosmos/interchain-security/issues/756)) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Cryptographic verification of equivocation](https://github.com/cosmos/interchain-security/issues/732) | ❌ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Jail throttling with retries](https://github.com/cosmos/interchain-security/issues/713) - consumer-side changes | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| [Jail throttling with retries](https://github.com/cosmos/interchain-security/issues/713) - [provider-side changes](https://github.com/cosmos/interchain-security/issues/1102) | ❌ | ❌ | ❌ | ✅ | ✅ | ✅ |
| [ICS epochs](https://cosmos.github.io/interchain-security/adrs/adr-014-epochs) | ❌ | ❌ | ❌ | ❌ | ✅ | ✅ |
