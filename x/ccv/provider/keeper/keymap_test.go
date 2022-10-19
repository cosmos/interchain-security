package keeper_test

import (
	"bytes"
	"testing"
)

func TKeyMapSerializationAndDeserialization(t *testing.T) {
}

// FuzzPrivateKeys will generate strings that can be used to seed
// new validator private keys, in a manner that ensures a strictly increasing
// order as per the lexicographic ordering of the staking module.
// This is needed to make sure that the lexicographic ordering is always
// consistent between the model and the SUT.
func FuzzPrivateKeys(f *testing.F) {
	f.Fuzz(func(t *testing.T, bz []byte) {
		k := cryptoEd25519.SeedSize
		// Ensure 4 keys are generated
		if len(bz) < 4*k {
			t.Skip()
		}
		// Map each byte to 'a' or 'b' characters
		for i, char := range bz {
			bz[i] = byte(int(char)%2 + int('a'))
		}
		var keys [][]byte
		// Get the staking module lexicographic bytes
		for i := 0; i < 4; i++ {
			keys = append(keys, getStakingKeyBytes(bz[i*k:i*k+k]))
		}
		good := true
		// Check if the bytes are ordered strictly descending
		for i := 0; i < 3; i++ {
			// the execution is good if the keys are sorted in descending order
			// Compare(a,b) === -1 IFF a > b
			good = good && bytes.Compare(keys[i], keys[i+1]) == 1
		}
		// If the bytes are ordered strictly descending
		// we can use them as validator key seeds for diff testing.
		if good {
			strings := make([]string, 4)
			for i := 0; i < 4; i++ {
				strings[i] = string(bz[i*k : i*k+k])
			}
			t.Errorf("[%s,\n%s,\n%s,\n%s]", strings[0], strings[1], strings[2], strings[3])
		}
	})
	/*
		Will output something like
			[
			bbaaaababaabbaabababbaabbbbbbaaa,
			abbbababbbabaaaaabaaabbbbababaab,
			bbabaabaabbbbbabbbaababbbbabbbbb,
			aabbbabaaaaababbbabaabaabbbbbbba
			]
		which can be used to generate validator private keys.
	*/
}
