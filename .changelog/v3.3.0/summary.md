*December 4th, 2023*

This release is state and api breaking.

Notable features of this release:
* Cryptohraphic-equivocation feature added to provider in [\#1340](https://github.com/cosmos/interchain-security/pull/1340) moves ICS towards untrusted consumers.
* Key assignment upgrades [\#1339](https://github.com/cosmos/interchain-security/pull/1339)
* Additional message validation and constraints for the core protocol [\#1460](https://github.com/cosmos/interchain-security/pull/1460)
* ICS quint model added [\#1336](https://github.com/cosmos/interchain-security/pull/1336)
* Upgrades to consumer genesis procedure [\#1324](https://github.com/cosmos/interchain-security/pull/1324)
This PR extends the consumer command with a `transform` subcommand that transform genesis outputs from provider on v1/2/3 into output that can be used by consumer on `>=v3.3.0`

```shell
# Example:
$ interchain-security-cd transform /path/to/ccv_consumer_genesis.json
```

