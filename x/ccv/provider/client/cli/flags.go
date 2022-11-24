package cli

import (
	flag "github.com/spf13/pflag"
)

const (
	FlagConsumerChainId  = "consumer-chain-id"
	FlagAddressValidator = "validator"
	FlagConsumerPubKey   = "consumer-pubkey"
	FlagNodeID           = "node-id"
	FlagIP               = "ip"
)

// common flagsets to add to various functions
var (
	fsValidator = flag.NewFlagSet("", flag.ContinueOnError)
)

func init() {
	fsValidator.String(FlagAddressValidator, "", "The Bech32 address of the validator")
}

// FlagSetPublicKey Returns the flagset for Public Key related operations.
func FlagSetPublicKey() *flag.FlagSet {
	fs := flag.NewFlagSet("", flag.ContinueOnError)
	fs.String(FlagConsumerPubKey, "", "The Protobuf JSON encoded public key to use for the consumer chain")
	return fs
}

// FlagSetPublicKey Returns the flagset for Public Key related operations.
func FlagSetConsumerChainId() *flag.FlagSet {
	fs := flag.NewFlagSet("", flag.ContinueOnError)
	fs.String(FlagConsumerChainId, "", "The chainId of the consumer chain")
	return fs
}
