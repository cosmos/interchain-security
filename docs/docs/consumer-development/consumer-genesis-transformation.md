---
sidebar_position: 6
---

# Consumer Genesis Transformation

Preparing a consumer chain for onboarding requires some information explaining how to run your chain. This includes a genesis file with CCV data where the CCV data is exported from the provider chain and added to the consumers genesis file (for more details check the documentaion on [Onboarding](./onboarding.md) and [Changeover](./changeover-procedure.md)).
In case that the provider chain is running an older version of the InterChainSecurity (ICS) module than the consumer chain the exported CCV data might need to be transformed to the format supported by the ICS implementation run on the consumer chain. This is the case if the cosumer chain runs consensus version 4 of ICS or later and the provider is running consensus version 3 or older of the ICS module.

To transform such CCV data follow the instructions below

## 1. Prerequisite
- Provider chain is running consensus version 3 or older of the ICS provider module
- Consumer is running consensus version 4 or later of the ICS consumer module.
- interchain-security-cd application complies to the version run on the consumer chain

## 2. Export the CCV data
Export the CCV data from the provider chain as descibed in the [Onboarding](./onboarding.md) and [Changeover](./changeover-procedure.md)) your following.
As a result the CCV data will be stored in a file in JSON format.

## 3. Transform CCV data
To transform the CCV data to the newer format run the following command.
```
interchain-security-cd genesis transform [genesis-file]
```
where 'genesis-file' is the path to the file containing the CCV data exported in [step 2](#2-export-the-ccv-data).
As a result the CCV data in the new format will be written to standard output.

Use the new CCV data as described in the procedure you're following.