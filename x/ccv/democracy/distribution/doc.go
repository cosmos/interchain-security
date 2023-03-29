/*
Package distribution defines a "wrapper" module around the Cosmos SDK's native
x/distribution module. In other words, it provides the exact same functionality as
the native module in that it simply embeds the native module.

The consumer chain should utilize the x/ccv/democracy/distribution module to perform democratic
actions such as participating and voting within the chain's governance system.
*/
package distribution
