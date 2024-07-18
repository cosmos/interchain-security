package simulation

import (
	"github.com/cosmos/cosmos-sdk/types/kv"
	"github.com/gogo/protobuf/codec"
)

// NewDecodeStore returns a decoder function closure that umarshals the KVPair's
// Value to the corresponding authz type.
func NewDecodeStore(cdc codec.Codec) func(kvA, kvB kv.Pair) string {
	return func(kvA, kvB kv.Pair) string {
		panic("TO BE IMPLEMENTED")
		return ""
	}
}
