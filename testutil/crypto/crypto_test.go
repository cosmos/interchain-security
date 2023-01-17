package crypto_test

import (
	"testing"

	testcrypto "github.com/cosmos/interchain-security/testutil/crypto"
	"github.com/stretchr/testify/require"
)

// TestCryptoIdentityAddresses tests that crypto identities have different
// consensus and validator addresses when generated from the same seed
func TestCryptoIdentityAddresses(t *testing.T) {
	keys := map[string]bool{}
	valAddrs := map[string]bool{}

	for i := 0; i < 99; i++ {
		ci := testcrypto.NewCryptoIdentityFromIntSeed(i)
		require.False(t, ci.SDKConsAddress().Equals(ci.SDKValAddress()))
		require.False(t, keys[ci.PrivKey.String()])
		require.False(t, valAddrs[ci.SDKValAddress().String()])

		keys[ci.PrivKey.String()] = true
		keys[ci.SDKValAddress().String()] = true
	}
}
