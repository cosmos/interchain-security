---
sidebar_position: 6
---

# Consumer Genesis Transformation

Preparing a consumer chain for onboarding requires some information explaining how to run your chain. This includes a genesis file with CCV data where the CCV data is exported from the provider chain and added to the consumers genesis file (for more details check the documentation on [Onboarding](./onboarding.md) and [Changeover](./changeover-procedure.md)).
In case that the provider chain is running an older version of the InterChainSecurity (ICS) module than the consumer chain - or vice versa - the exported CCV data might need to be transformed to the format supported by the ICS implementation run on the consumer chain. This is the case if the consumer chain runs version 4 of ICS or later and the provider is running version 3 or older of the ICS module.

Check the [compatibility notes](../../../RELEASES.md#backwards-compatibility) for known incompatibilities between provider and consumer versions and indications if a consumer genesis transformation is required.

To transform such CCV data follow the instructions below

## 1. Prerequisite
- used provider and consumer versions require transformation step as indicated in in the [compatibility notes](../../../RELEASES.md#backwards-compatibility)
- interchain-security-cd application supports the versions used by the consumer and provider

## 2. Export the CCV data
Export the CCV data from the provider chain as described in the [Onboarding](./onboarding.md) and [Changeover](./changeover-procedure.md) your following.
As a result the CCV data will be stored in a file in JSON format.

## 3. Transform CCV data
To transform the CCV data
- to the format supported by the current version of the consumer run the following command:
    ```
    interchain-security-cd genesis transform [genesis-file]
    ```
    where 'genesis-file' is the path to the file containing the CCV data exported in [step 2](#2-export-the-ccv-data).
    As a result the CCV data in the new format will be written to standard output.
- a specific target version of a consumer run the following command:
    ```
    interchain-security-cd genesis transform --to <target_version> [genesis-file]

    ```
    where `<target_version` is the ICS version the consumer chain is running.
    Use `interchain-security-cd genesis transform --help` to get more details about supported target versions and more.


Use the new CCV data as described in the procedure you're following.

