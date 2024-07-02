package main

import (
	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
)

const (
	PROVIDER = "provider"
)

// getIndexOfString returns the index of the first occurrence of the given string
// in the given slice, or -1 if the string is not found.
func getIndexOfString(s string, slice []string) int {
	for i, v := range slice {
		if v == s {
			return i
		}
	}
	return -1
}

func init() {
	//	tokens === power
	sdk.DefaultPowerReduction = math.NewInt(1)
}
