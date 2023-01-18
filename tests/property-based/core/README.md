# Property-Based Testing for Interchain Security normal operation

## What is this?

Some code which is an example of how you can test very high level properties of Interchain Security using property based testing, and in particular the [rapid](https://github.com/flyingmutant/rapid) golang library for property based testing.

## Why is this interesting?

It's a concrete demonstration of using PBT in the interchain security context to achieve a high coverage in a very small amount of code. Additionally, the system is viewed very much as a black box so this test should not need to change hardly at all.

## Where can we learn about property based testing?

See [Tutorial.md](https://github.com/cosmos/interchain-security/blob/danwt/pbt-prototype/tests/pbt/tutorial.md) for a tutorial and links to more resources about the property based testing idea and how to use the rapid library. See [Method.md](https://github.com/cosmos/interchain-security/blob/danwt%2Fdifftest-core-non-functional-model-and-docs-improvements/tests/difference/core/docs/METHOD.md) to understand diff-testing, which is not the same as PBT, but gives context. Also, Method.md DOES contain a section comparing diff testing and property based testing.

## What does this directory contain?

One property based test using the rapid library in pbt_test.go. The test relies on some state setup, which is all done in setup/setup.go. There is a normal unit test for the setup itself in setup/setup_test.go.

The property based test takes 1 provider chain and 1 consumer chain which are connected and which share the same validator set. It simulates an ibc channel between them. Then, it does random actions against the system to check that Validator Set Replication property holds.

The actions are

- Delegate
- Undelegate
- Redelegate
- Unjail
- Consumer Initiated Slash
- Update Light Client
- Deliver sent packets from one chain to another

The property(s) are

- Validator Set Replication

## What can we do with this?

Whatever you like. If you find it interesting and useful you can bring it into the main branch. Also, you may consider moving towards a PBT based approach in future, as opposed to a diff testing one. See [Method.md](https://github.com/cosmos/interchain-security/blob/danwt%2Fdifftest-core-non-functional-model-and-docs-improvements/tests/difference/core/docs/METHOD.md) for more info.
