# Info for Validators

Validators may want to read this document.

##  Key Assignment

The key assignment feature enables validators to use different consensus keys for each consumer chain. The feature allows validators to submit an AssignConsumerKey transaction to the provider chain. Pseudocode for type:

```txt
message MsgAssignConsumerKey {
  // The chain id of the consumer chain to assign a consensus public key to
  string chain_id;
  // The validator's operator address on the provider
  string provider_addr;
  // The validator's consensus public key to use on the consumer
  google.protobuf.Any;
}
```

On receiving the transaction, if the assignment is valid, the provider will use the assigned consensus key when it sends future voting power updates to the consumer that involve the validator.

There are some rules about which keys can and can't be assigned:

1. validator A cannot assign consumer key K to consumer chain X if there is already validator B (B!=A) using K _on the provider_
2. validator A cannot assign consumer key K to consumer chain X if there is already a validator B using K on X

Note that keys can be assigned for a chain X before the addition proposal for X has passed.

There are also some added rule(s) about creating _new_ validators.

1. A new validator on the provider cannot use a consensus key K if K is already used by any validator on any consumer chain
