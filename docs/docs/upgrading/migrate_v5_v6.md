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

#### Consumer addition proposal

```shell
interchain-security-pd tx gov submit-proposal <proposal_file.json>
```

####  Consumer removal proposal

```shell
interchain-security-pd tx gov submit-proposal <proposal_file.json>
```

####  Consumer modification proposal
```shell
interchain-security-pd tx gov submit-proposal <proposal_file.json>
```

Run `interchain-security-pd tx gov draft-proposal` command and select in `other` one of the following
message types to generate a draft example:
- `/interchain_security.ccv.provider.v1.MsgConsumerAddition`
- `/interchain_security.ccv.provider.v1.MsgConsumerModification`
- `/interchain_security.ccv.provider.v1.MsgConsumerRemoval`
