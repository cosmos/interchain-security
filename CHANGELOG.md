# CHANGELOG

## [Unreleased]

Note: Some PRs in the unreleased section may reappear from the released sections of some releases below. This is due to the fact that ICS v1.1.0 deviates from the commit ordering of the main branch, and all other releases thereafter are based on v1.1.0.

The ICS v1.3.0 release will be based on the main branch, and will not have this issue. v1.3.0 will also contain all the accumulated PRs from the various releases below. After v1.3.0, we plan to revamp release practices, and how we modularize the repo for consumer/provider.

TODO: Feature EPICs that were completed and will be added within the next release (standalone to consumer, soft opt out, etc.)

* (deps) Bump hermes [#921](https://github.com/cosmos/interchain-security/pull/921)
* (deps) bump gaurav-nelson/github-action-markdown-link-check from 1.0.13 to 1.0.15 [#928](https://github.com/cosmos/interchain-security/pull/928)
* (chore) update codeowners [#892](https://github.com/cosmos/interchain-security/pull/892)
* (fix) multisig for assigning consumer key, use json [#916](https://github.com/cosmos/interchain-security/pull/916)
* (chore) update golangci-lint configuration [#914](https://github.com/cosmos/interchain-security/pull/914)
* (ci) add check for markdown links [#912](https://github.com/cosmos/interchain-security/issues/912)
* (docs) Update links, update docs on withdraw rewards [#910](https://github.com/cosmos/interchain-security/pull/910)
* (chore) buf.yaml should specify the repository [#872](https://github.com/cosmos/interchain-security/pull/872)
* (deps) Bump github.com/cosmos/ibc-go/v4 from 4.3.0 to 4.4.0 [#902](https://github.com/cosmos/interchain-security/pull/902)
* (feat) Add warnings when provider unbonding is shorter than consumer unbonding [#858](https://github.com/cosmos/interchain-security/pull/858)
* (chore) use go 1.19 [#899](https://github.com/cosmos/interchain-security/pull/899)
* (docs) guidelines on large contributions and feature branches [#868](https://github.com/cosmos/interchain-security/pull/868)
* (docs) Create security doc [#871](https://github.com/cosmos/interchain-security/pull/871)
* (docs) Update contributing guidelines [#859](https://github.com/cosmos/interchain-security/pull/859)
* (docs) fix comment [#863](https://github.com/cosmos/interchain-security/pull/863)
* (chore) Various linting config changes [#860](https://github.com/cosmos/interchain-security/pull/860)
* (feat) Standalone to consumer changeover - recycle existing transfer channel [#832](https://github.com/cosmos/interchain-security/pull/832)
* (deps) Bump IBC [862](https://github.com/cosmos/interchain-security/pull/862)
* (testing) Add tests for soft opt out [#857](https://github.com/cosmos/interchain-security/pull/857)
* (chore) Use go 1.20 [#840](https://github.com/cosmos/interchain-security/pull/840)
* (chore) fix make proto-update-deps [#830](https://github.com/cosmos/interchain-security/pull/830)
* (refactor) Remove GenPubKey [#839](https://github.com/cosmos/interchain-security/pull/839)
* (refactor) Move /utils to /types [#856](https://github.com/cosmos/interchain-security/pull/856)
* (deps) Bump github.com/spf13/cobra from 1.6.1 to 1.7.0 [#855](https://github.com/cosmos/interchain-security/pull/855)
* (deps) Bump github.com/stretchr/testify from 1.8.1 to 1.8.2 [#854](https://github.com/cosmos/interchain-security/pull/854)
* (feat) Standalone to consumer changeover - staking functionalities [#794](https://github.com/cosmos/interchain-security/pull/794)
* (fix) prevent provider from sending VSCPackets with multiple updates for the same validator [#850](https://github.com/cosmos/interchain-security/pull/850)
* (docs) code and docs mismatch [#844](https://github.com/cosmos/interchain-security/pull/844)
* (testing) Use caching in dockerfiles [#843](https://github.com/cosmos/interchain-security/pull/843)
* (feat) Soft opt out [#833](https://github.com/cosmos/interchain-security/issues/833)
* (fix) Correctly handle VSC packet with duplicate val updates on consumer [#846](https://github.com/cosmos/interchain-security/pull/846)
* (deps) bump sdk to v0.45.15.ics [#805](https://github.com/cosmos/interchain-security/pull/805)
* (refactor) Remove starport config [#841](https://github.com/cosmos/interchain-security/pull/841)
* (refactor) Remove RegisterSdkCryptoCodecInterfaces [#838](https://github.com/cosmos/interchain-security/pull/838)
* (chore) fix makefile [#837](https://github.com/cosmos/interchain-security/pull/837)
* (deps) Bump github.com/spf13/cobra from 1.6.1 to 1.7.0 [#834](https://github.com/cosmos/interchain-security/pull/834)
* (deps) bump IBC to v4.3.0 [#823](https://github.com/cosmos/interchain-security/pull/823)
* (docs) fix typos and broken links [#829](https://github.com/cosmos/interchain-security/pull/829)
* (refactor) more linting [#820](https://github.com/cosmos/interchain-security/pull/820)
* (refactor) linting [#810](https://github.com/cosmos/interchain-security/pull/810)
* (refactor) Remove spm module [#812](https://github.com/cosmos/interchain-security/pull/812)
* (feat) Standalone to consumer changeover part 1 [#757](https://github.com/cosmos/interchain-security/pull/757)
* (deps) Bump webpack from 5.75.0 to 5.76.3 in /docs [#797](https://github.com/cosmos/interchain-security/pull/797)
* (chore) Swap names of e2e and integration tests [#681](https://github.com/cosmos/interchain-security/pull/681)
* (testing) Improved key tests [#787](https://github.com/cosmos/interchain-security/pull/787)
* (chore) Change automated test run policy to run on pull req [#807](https://github.com/cosmos/interchain-security/pull/807)
* (docs) Update consume chain governance documentation [commit](https://github.com/cosmos/interchain-security/commit/9c25ab51dc1c0311bd036935bab7478e6a2f2b71)
* (fix) fix fix StopConsumerChain not running in cachedContext [#802](https://github.com/cosmos/interchain-security/pull/802). Also in earlier releases with different commit order!
* (docs) Introduce docs website [#759](https://github.com/cosmos/interchain-security/pull/759)
* (deps) Bump google.golang.org/protobuf from 1.28.2-0.20220831092852-f930b1dc76e8 to 1.30.0 [#793](https://github.com/cosmos/interchain-security/pull/793)
* (deps) Bump actions/setup-go from 3 to 4 [#792](https://github.com/cosmos/interchain-security/pull/792)
* (fix) Ser correct byte prefix for SlashLogKey [#786](https://github.com/cosmos/interchain-security/pull/786)
* (chore) add Makefile target to generate mocks [#769](https://github.com/cosmos/interchain-security/pull/769)
* (deps) Bump github.com/golang/protobuf from 1.5.2 to 1.5.3 [#779](https://github.com/cosmos/interchain-security/pull/779)
* (deps) Bump github.com/tidwall/gjson from 1.14.0 to 1.14.4 [#776](https://github.com/cosmos/interchain-security/pull/776)
* (deps) Bump actions/checkout from 2 to 3 [#775](https://github.com/cosmos/interchain-security/pull/775)
* (deps) Bump actions/setup-go from 2 to 3 [#774](https://github.com/cosmos/interchain-security/pull/774)
* (feature) Improve keeper field validation [#766](https://github.com/cosmos/interchain-security/pull/766)
* (deps) Bump json5 from 2.2.1 to 2.2.3 in /tests/difference/core/model [#762](https://github.com/cosmos/interchain-security/pull/762)
* (deps) Bump golang.org/x/net from 0.5.0 to 0.7.0 [#763](https://github.com/cosmos/interchain-security/pull/763)
* (chore) Add depedabot config [#764](https://github.com/cosmos/interchain-security/pull/764)
* (chore) disable sonarcloud on dependabot PRs and forks [#768](https://github.com/cosmos/interchain-security/pull/768)
* (chore) revert build.yml changes [#767](https://github.com/cosmos/interchain-security/pull/767)
* (chore) update build.yml [commit](https://github.com/cosmos/interchain-security/commit/019f70fa7e83bd29ab94f4d1da77ba7aa49bba9c)
* (docs) Tidy docs directory [#758](https://github.com/cosmos/interchain-security/pull/758)
* (docs) Update issue template [#755](https://github.com/cosmos/interchain-security/pull/755)
* (testing) gaia docker tests with custom sdk [#737](https://github.com/cosmos/interchain-security/pull/737)
* (testing) gaia as provider in docker tests [#735](https://github.com/cosmos/interchain-security/pull/735)
* (docs) Contributing guidelines [#744](https://github.com/cosmos/interchain-security/pull/744)
* (refactor) Key assignment type safety [#725](https://github.com/cosmos/interchain-security/pull/725)
* (refactor) Update protos and fix deps [#752](https://github.com/cosmos/interchain-security/pull/752)
* (api) Add consumer QueryParams [#746](https://github.com/cosmos/interchain-security/pull/746)
* (fix) Nits from audit [#743](https://github.com/cosmos/interchain-security/pull/743)
* (feature) New validation for keeper fields [#740](https://github.com/cosmos/interchain-security/pull/740)

## v1.2.0-multiden

The first release candidate for a fix built on top of v1.2.0, intended for consumers. This release adds a list of denoms on the consumer that are allowed to be sent to the provider as rewards. This prevents a potential DOS attack that was discovered during the audit of Replicated Security performed by Oak Security and funded by the Cosmos Hub community through Proposal 687. In an effort to move quickly, this release also includes a multisig fix that is effective only for provider. It shouldn't affect the consumer module.

Note PRs were made in a private security repo.

[full diff](https://github.com/cosmos/interchain-security/compare/v1.2.0...v1.2.0-multiden-rc0)

## v1.1.0-multiden

This release combines two fixes on top of v1.1.0, that we judged were urgent to get onto the Cosmos Hub before the launch of the first ICS consumer chain. This is an emergency release intended for providers.

The first fix is to enable the use of multisigs and Ledger devices when assigning keys for consumer chains. The second is to prevent a possible DOS vector involving the reward distribution system.

Note PRs were made in a private security repo.

[full diff](https://github.com/cosmos/interchain-security/compare/v1.1.0...release/v1.1.0-multiden)

### Multisig fix

On April 25th (a week and a half ago), we began receiving reports that validators using multisigs and Ledger devices were getting errors reading Error: unable to resolve type URL /interchain_security.ccv.provider.v1.MsgAssignConsumerKey: tx parse error when attempting to assign consensus keys for consumer chains.

We quickly narrowed the problem down to issues having to do with using the PubKey type directly in the MsgAssignConsumerKey transaction, and Amino (a deprecated serialization library still used in Ledger devices and multisigs) not being able to handle this. We attempted to fix this with the assistance of the Cosmos-SDK team, but after making no headway for a few days, we decided to simply use a JSON representation of the PubKey in the transaction. This is how it is usually represented anyway. We have verified that this fixes the problem.

### Distribution fix

The ICS distribution system works by allowing consumer chains to send rewards to a module address on the provider called the FeePoolAddress. From here they are automatically distributed to all validators and delegators through the distribution system that already exists to distribute staking rewards. The FeePoolAddress is usually blocked so that no tokens can be sent to it, but to enable ICS distribution we had to unblock it.

We recently realized that unblocking the FeePoolAddress could enable an attacker to send a huge number of different denoms into the distribution system. The distribution system would then attempt to distribute them all, leading to out of memory errors. Fixing a similar attack vector that existed in the distribution system before ICS led us to this realization.

To fix this problem, we have re-blocked the FeePoolAddress and created a new address called the ConsumerRewardsPool. Consumer chains now send rewards to this new address. There is also a new transaction type called RegisterConsumerRewardDenom. This transaction allows people to register denoms to be used as rewards from consumer chains. It costs 10 Atoms to run this transaction.The Atoms are transferred to the community pool. Only denoms registered with this command are then transferred to the FeePoolAddress and distributed out to delegators and validators.

## v1.2.1

* (fix) Remove SPM [#812](https://github.com/cosmos/interchain-security/pull/812)
* (refactor) Key assignment type safety [#725](https://github.com/cosmos/interchain-security/pull/725)

## v1.2.0

Date: April 13th, 2023

* (feat) Soft opt-out [#833](https://github.com/cosmos/interchain-security/pull/833)
* (fix) Correctly handle VSC packet with duplicate val updates on consumer [#846](https://github.com/cosmos/interchain-security/pull/846)
* (chore) bump: sdk v0.45.15-ics [#805](https://github.com/cosmos/interchain-security/pull/805)
* (api) add interchain security consumer QueryParams [#746](https://github.com/cosmos/interchain-security/pull/746)

## v1.1.1

* (fix) Remove SPM [#812](https://github.com/cosmos/interchain-security/pull/812)
* (refactor) Key assignment type safety [#725](https://github.com/cosmos/interchain-security/pull/725)

## v1.1.0

Date: March 24th, 2023

* (fix) StopConsumerChain not running in cachedContext [#802](https://github.com/cosmos/interchain-security/pull/802)

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
