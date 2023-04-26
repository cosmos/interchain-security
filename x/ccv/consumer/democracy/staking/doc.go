/*
Package staking defines a "wrapper" module around the Cosmos SDK's native
x/staking module. In other words, it provides the exact same functionality as
the native module in that it simply embeds the native module. However, it
overrides two core methods, `InitGenesis` and `EndBlock`. Specifically, these
methods perform no-ops and return no validator set updates, as validator sets
are tracked by the consumer chain's x/ccv/consumer module.

The consumer chain should utilize the x/ccv/democracy/staking module to perform democratic
actions such as participating and voting within the chain's governance system.
*/
package staking
