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
// any of which should be a single byte.
func getSingleByteKeys() [][]byte {

	keys := make([][]byte, 16)
	i := 0

	keys[i], i = PortKey(), i+1
	keys[i], i = MaturedUnbondingOpsKey(), i+1
	keys[i], i = ValidatorSetUpdateIdKey(), i+1
	keys[i], i = ChainToChannelPrefix(), i+1
	keys[i], i = ChannelToChainPrefix(), i+1
	keys[i], i = ChainToClientPrefix(), i+1
	keys[i], i = PendingClientPrefix(), i+1
	keys[i], i = PendingStopProposalPrefix(), i+1
	keys[i], i = UnbondingOpPrefix(), i+1
	keys[i], i = UnbondingOpIndexPrefix(), i+1
	keys[i], i = ValsetUpdateBlockHeightPrefix(), i+1
	keys[i], i = ConsumerGenesisPrefix(), i+1
	keys[i], i = SlashAcksPrefix(), i+1
	keys[i], i = InitChainHeightPrefix(), i+1
	keys[i], i = PendingVSCsPrefix(), i+1
	keys[i] = LockUnbondingOnTimeoutPrefix()

	return keys
}
