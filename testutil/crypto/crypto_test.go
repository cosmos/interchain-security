package crypto

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestLike(t *testing.T) {

	eq := func(bz0 []byte, bz1 []byte) bool {
		if len(bz0) != len(bz1) {
			return false
		}
		for i := range bz0 {
			if bz0[i] != bz1[i] {
				return false
			}
		}
		return true
	}

	id := NewCryptoIdentityFromIntSeed(0)
	abciAddressBytes := id.ABCIAddressBytes()
	sdkOperator := id.SDKOperator()
	sdkValAddressString := id.SDKValAddressString()
	sdkValAddress := id.SDKValAddress()
	sdkConsAddress := id.SDKConsAddress()

	require.False(t, eq(abciAddressBytes, []byte(sdkValAddressString)))

	require.True(t, eq(abciAddressBytes, sdkConsAddress))
	require.True(t, eq(abciAddressBytes, sdkValAddress))
	require.True(t, eq(abciAddressBytes, sdkOperator))

	require.True(t, string(sdkValAddress) == sdkValAddressString)

}
