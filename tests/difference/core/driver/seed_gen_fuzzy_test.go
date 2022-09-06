package core_test

import (
	"bytes"
	"testing"

	cryptoEd25519 "crypto/ed25519"

	cosmosEd25519 "github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	mock "github.com/cosmos/ibc-go/v3/testing/mock"
	tmtypes "github.com/tendermint/tendermint/types"
)

func GetPV(seed []byte) mock.PV {
	//lint:ignore SA1019 We don't care because this is only a test.
	return mock.PV{PrivKey: &cosmosEd25519.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}
}

// getStakingKeyBytes takes seed bytes which can be be used to create
// a validator and returns the bytes that the staking module uses for
// lexicographic comparison using that validator
func getStakingKeyBytes(bz []byte) []byte {
	pv := GetPV(bz)
	pubKey, _ := pv.GetPubKey()
	val := tmtypes.NewValidator(pubKey, 0)
	addr, _ := sdk.ValAddressFromHex(val.Address.String())
	PK := pv.PrivKey.PubKey()
	valAddr, _ := sdk.ValAddressFromBech32(addr.String())
	validator, _ := stakingtypes.NewValidator(valAddr, PK, stakingtypes.Description{})
	key := stakingtypes.GetValidatorsByPowerIndexKey(validator, sdk.DefaultPowerReduction)
	return key
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
