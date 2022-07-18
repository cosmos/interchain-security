package difftest_test

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
	return mock.PV{&cosmosEd25519.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}
}

func getStakingKey(pv mock.PV) []byte {
	pubKey, _ := pv.GetPubKey()
	val := tmtypes.NewValidator(pubKey, 0)
	addr, _ := sdk.ValAddressFromHex(val.Address.String())
	PK := pv.PrivKey.PubKey()
	valAddr, _ := sdk.ValAddressFromBech32(addr.String())
	validator, _ := stakingtypes.NewValidator(valAddr, PK, stakingtypes.Description{})
	key := stakingtypes.GetValidatorsByPowerIndexKey(validator, sdk.DefaultPowerReduction)
	return key
}

func FuzzPrivateKeys(f *testing.F) {
	f.Fuzz(func(t *testing.T, bz []byte) {
		k := cryptoEd25519.SeedSize
		if len(bz) < 4*k {
			t.Skip()
		}
		for i, char := range bz {
			bz[i] = byte(int(char)%2 + int('a'))
		}
		var keys [][]byte
		for i := 0; i < 4; i++ {
			pv := GetPV(bz[i*k : i*k+k])
			keys = append(keys, getStakingKey(pv))
		}
		good := true
		for i := 0; i < 3; i++ {
			// the execution is good if the keys are sorted in descending order
			// Compare(a,b) === -1 IFF a > b
			good = good && bytes.Compare(keys[i], keys[i+1]) == 1
		}
		if good {
			strings := make([]string, 4)
			for i := 0; i < 4; i++ {
				strings[i] = string(bz[i*k : i*k+k])
			}
			t.Errorf("[%s,\n%s,\n%s,\n%s]", strings[0], strings[1], strings[2], strings[3])
		}
	})
	/*
		[
		bbaaaababaabbaabababbaabbbbbbaaa,
		abbbababbbabaaaaabaaabbbbababaab,
		bbabaabaabbbbbabbbaababbbbabbbbb,
		aabbbabaaaaababbbabaabaabbbbbbba
		]
	*/
}

func FuzzConfirm(f *testing.F) {
	// staking/types/validator.go::RemoveDelShares is busted
	f.Fuzz(func(t *testing.T, _ int) {
		var v stakingtypes.Validator
		v.Tokens = sdk.NewInt(27500)
		valShares, err := sdk.NewDecFromStr("50000.000000000000000000")
		if err != nil {
			t.Fatal(err)
		}
		v.DelegatorShares = valShares
		delShares, err := sdk.NewDecFromStr("18181.818181818181818181")
		if err != nil {
			t.Fatal(err)
		}
		// issued := v.TokensFromShares(delShares).TruncateInt()
		issued := (delShares.MulInt(v.Tokens)).Quo(v.DelegatorShares).TruncateInt()
		if !(sdk.NewInt(9999).Equal(issued)) {
			t.Fatal(issued)
		}
	})
}

func TestDec(t *testing.T) {
	// staking/types/validator.go::RemoveDelShares
	var v stakingtypes.Validator
	v.Tokens = sdk.NewInt(27500)
	valShares, err := sdk.NewDecFromStr("50000.000000000000000000")
	if err != nil {
		t.Fatal(err)
	}
	v.DelegatorShares = valShares
	delShares, err := sdk.NewDecFromStr("18181.818181818181818181")
	if err != nil {
		t.Fatal(err)
	}
	// issued := v.TokensFromShares(delShares).TruncateInt()
	issued := (delShares.MulInt(v.Tokens)).Quo(v.DelegatorShares).TruncateInt()
	if !(sdk.NewInt(9999).Equal(issued)) {
		t.Fatal(issued)
	}
}
