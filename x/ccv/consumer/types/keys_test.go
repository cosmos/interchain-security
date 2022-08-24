package types

import (
	"testing"

	"github.com/stretchr/testify/require"
)

// Tests that all singular keys, or prefixes to fully resolves keys are a single byte long,
// preventing injection attacks into restricted parts of a full store.
func TestSameLength(t *testing.T) {

	keys := getSingleByteKeys()

	for _, keyByteArray := range keys {
		require.Equal(t, 1, len(keyByteArray))
	}
}

// Tests that all singular keys, or prefixes to fully resolves keys are non duplicate byte values.
func TestNoDuplicates(t *testing.T) {

	keys := getSingleByteKeys()

	for i, keyByteArray := range keys {
		keys[i] = nil
		require.NotContains(t, keys, keyByteArray)
	}
}

// Returns all singular keys, or prefixes to fully resolved keys,
// any of which should be a single, unique byte.
func getSingleByteKeys() [][]byte {

	keys := make([][]byte, 12)
	i := 0

	keys[i], i = PortKey(), i+1
	keys[i], i = LastDistributionTransmissionKey(), i+1
	keys[i], i = UnbondingTimeKey(), i+1
	keys[i], i = ProviderClientIDKey(), i+1
	keys[i], i = ProviderChannelKey(), i+1
	keys[i], i = PendingChangesKey(), i+1
	keys[i], i = []byte{HistoricalInfoBytePrefix}, i+1
	keys[i], i = []byte{PacketMaturityTimeBytePrefix}, i+1
	keys[i], i = []byte{HeightValsetUpdateIDBytePrefix}, i+1
	keys[i], i = []byte{OutstandingDowntimeBytePrefix}, i+1
	keys[i], i = []byte{PendingSlashRequestsBytePrefix}, i+1
	keys[i] = []byte{CrossChainValidatorBytePrefix}

	return keys
}
