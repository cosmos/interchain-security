# Replicated Security v3.3.0 Release Notes

❗ ***Note this release is ONLY relevant to providers***

## 📝 Changelog

Check out the [changelog](https://github.com/cosmos/interchain-security/blob/v3.3.0/CHANGELOG.md) for a list of relevant changes or [compare all changes](https://github.com/cosmos/interchain-security/compare/v3.2.0...v3.3.0) from last release.

## 🚀 Highlights

<!-- Add any highlights of this release -->

This release introduces the following noteworthy changes:

- The cryptographic verification of equivocation feature is ported to SDK 0.47. 
  The feature is already running on the Cosmos Hub as part of the [v2.4.0-lsm](https://github.com/cosmos/interchain-security/releases/tag/v2.4.0-lsm) release. 

- It splits out consumer genesis state to reduce shared data between provider and consumer.
  As a result, the consumer CCV genesis state obtained from the provider chain needs to be transformed to be compatible with different versions of consumer chains. For more details, see the [documentation](https://cosmos.github.io/interchain-security/consumer-development/consumer-genesis-transformation).

- A query (`QueryAllPairsValConAddrByConsumerChainID`) is added to get a list of all assigned consumer keys for a given consumer `chainId`. For more details, see the [documentation](https://cosmos.github.io/interchain-security/features/key-assignment).

## ❤️ Contributors

* Decentrio ([@decentriolabs](https://twitter.com/decentriolabs))
* Informal Systems ([@informalinc](https://twitter.com/informalinc))

This list is non-exhaustive and ordered alphabetically.  
Thank you to everyone who contributed to this release!