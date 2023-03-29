/*
Package governance defines a "wrapper" module around the Cosmos SDK's native
x/governance module. In other words, it provides the exact same functionality as
the native module in that it simply embeds the native module. However, it
overrides `EndBlock` core method to remove forbidden governance proposals from the
storage(s) before the original `EndBlock` method from the native module is called.

The consumer chain should utilize the x/ccv/democracy/governance module to perform democratic
actions such as participating and voting within the chain's governance system.
*/
package governance
