package crypto_test

import (
	"testing"

	testcrypto "github.com/cosmos/interchain-security/testutil/crypto"
	"github.com/stretchr/testify/require"
)

// TestCryptoIdentityAddresses tests that crypto identities have different
// consensus and validator addresses when using the same random seed.
// It also briefly verifies that there is no collision when generating
// multiple crypto identities.
func TestCryptoIdentityAddresses(t *testing.T) {
	keys := map[string]bool{}
	valAddrs := map[string]bool{}

	for i := 0; i < 99; i++ {
		ci := testcrypto.NewCryptoIdentityFromIntSeed(i)
		require.False(t, ci.SDKConsAddress().Equals(ci.SDKValOpAddress()))
		require.False(t, keys[ci.PrivKey.String()])
		require.False(t, valAddrs[ci.SDKValOpAddress().String()])

		keys[ci.PrivKey.String()] = true
		keys[ci.SDKValOpAddress().String()] = true
	}
}
