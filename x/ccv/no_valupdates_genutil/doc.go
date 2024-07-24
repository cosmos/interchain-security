/*
Package genutil defines a "wrapper" module around the Cosmos SDK's native
x/genutil module. In other words, it provides the exact same functionality as
the native module in that it simply embeds the native module. However, it
overrides `InitGenesis` which will return no validator set updates. Instead,
it is assumed that some other module will provide the validator set updates.
*/
package genutil
