package crypto_test

import (
	"encoding/binary"
	"fmt"
	"testing"

	testcrypto "github.com/cosmos/interchain-security/testutil/crypto"
)

func TestCryptoIdentity(t *testing.T) {
	iUint64 := uint64(1)
	seed := []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	binary.LittleEndian.PutUint64(seed[:8], iUint64)
	fmt.Println(seed, len(seed), cap(seed))

	testcrypto.CreateOpAddressFromByteSeed(seed)

	// fmt.Println(ci.PrivKey.Bytes())
	// fmt.Println(seed, len(seed), cap(seed))

	// iUint64 = uint64(2)
	// seed = []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	// binary.LittleEndian.PutUint64(seed[:8], iUint64)
	// ci = testcrypto.NewCryptoIdentityFromBytesSeed(seed)

	// iUint64 = uint64(2)

	// binary.LittleEndian.PutUint64(seed[:8], iUint64)
	// fmt.Println(string(seed))

	// fmt.Println(ci.PrivKey.Bytes())
	// fmt.Println(seed, len(seed), cap(seed))
	// ci := testcrypto.NewCryptoIdentityFromIntSeed(1)
	// ci1 := testcrypto.NewCryptoIdentityFromIntSeed(2)

	// fmt.Println(ci.PrivKey.Bytes())
	// fmt.Println(ci1.PrivKey.Bytes())
}
