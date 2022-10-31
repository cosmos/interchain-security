package cli

import (
	flag "github.com/spf13/pflag"
)

const (
	FlagChainId          = "validator"
	FlagAddressValidator = "validator"
	FlagPubKey           = "pubkey"
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
	fs.String(FlagPubKey, "", "The validator's Protobuf JSON encoded public key")
	return fs
}
