---
sidebar_position: 1
---

# Upgrading to ICS v6.x from v5.x

ICS specific changes are outlined below.

Pre-requisite version for this upgrade: any from the `v5.x` release line.

## Note

## Provider

### Migration (v5 -> v6)

ConensusVersion was bumped to `6`.

### Governance proposals

To submit a proposal to add/modify/remove a consumer use the following command
```shell
interchain-security-pd tx gov submit-proposal <proposal_file.json>
```

Run `interchain-security-pd tx gov draft-proposal` command and select in `other` one of the following
message types to generate a draft proposal json file:
- `/interchain_security.ccv.provider.v1.MsgConsumerAddition`
- `/interchain_security.ccv.provider.v1.MsgConsumerModification`
- `/interchain_security.ccv.provider.v1.MsgConsumerRemoval`
- `/interchain_security.ccv.provider.v1.MsgChangeRewardDenoms`
