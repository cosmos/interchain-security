package crypto_test

import (
	"testing"

	testcrypto "github.com/cosmos/interchain-security/testutil/crypto"
	"github.com/stretchr/testify/require"
)

// TestNewCryptoIdentityFromIntSeed tests that crypto identities are generated
// with different validator consensus and operator addresses using a given integer seed,
// and also checks for any collisions in addresses and private keys when generating
// multiple crypto identities with different seeds.
func TestNewCryptoIdentityFromIntSeed(t *testing.T) {
	keys := map[string]bool{}
	valAddrs := map[string]bool{}

	for i := 0; i < 99; i++ {
		ci := testcrypto.NewCryptoIdentityFromIntSeed(i)
		require.False(t, ci.SDKValConsAddress().Equals(ci.SDKValOpAddress()))
		require.False(t, keys[ci.PrivKey.String()])
		require.False(t, valAddrs[ci.SDKValOpAddress().String()])

		keys[ci.PrivKey.String()] = true
		keys[ci.SDKValOpAddress().String()] = true
	}
}
