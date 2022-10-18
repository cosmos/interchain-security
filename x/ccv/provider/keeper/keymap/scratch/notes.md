///////// OK
// When a consumer receives an update, it receives the tendermint public key
// it does THIS
addr := utils.GetChangePubKeyAddress(change)
consAddr := sdk.ConsAddress(addr)
// to get the cons address

// if I change keymap to store a map of cons addresses, then
// the slash will send a cons address
// the reverse cons address can be looked up

// in order to send updates, convert the output of the staking module
// to the address using the above function
// get the corresponding consumer address.. but then still need the consumer tendermint key...