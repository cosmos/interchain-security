# Info for Validators

Validators may want to read this

##  Key Assignment

The key assignment feature enables validators to use different consensus keys for each consumer chain. The provider allows validators to submit an AssignConsumerKey transaction to the provider chain. Pseudocode for type:

```txt
message MsgAssignConsumerKey {
  // The chain id of the consumer chain to assign a consensus public key to
  string chain_id;
  // The validator address on the provider
  string provider_addr;
  // The consensus public key to use on the consumer
  google.protobuf.Any;
}
```

On receiving the transaction, if the assignment is valid, the provider will use the assigned consensus key when it sends future voting power updates to the consumer that involve the validator.

There are some rules about which keys can and can't be assigned:

1.
