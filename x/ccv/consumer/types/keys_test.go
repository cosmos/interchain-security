package types_test

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	consumertypes "github.com/cosmos/interchain-security/v7/x/ccv/consumer/types"
)

// Tests that all singular keys, or prefixes to fully resolves keys are non duplicate byte values.
func TestNoDuplicates(t *testing.T) {
	prefixes := consumertypes.GetAllKeyPrefixes()
	seen := []byte{}

	for _, prefix := range prefixes {
		require.NotContains(t, seen, prefix, "Duplicate key prefix: %v", prefix)
		seen = append(seen, prefix)
	}
}

// Test that the value of all byte prefixes is preserved
func TestPreserveBytePrefix(t *testing.T) {
	i := 0
	require.Equal(t, byte(0), consumertypes.PortKey()[0])
	i++
	require.Equal(t, byte(1), consumertypes.LastDistributionTransmissionKey()[0])
	i++
	require.Equal(t, byte(2), consumertypes.UnbondingTimeKey()[0])
	i++
	require.Equal(t, byte(3), consumertypes.ProviderClientIDKey()[0])
	i++
	require.Equal(t, byte(4), consumertypes.ProviderChannelIDKey()[0])
	i++
	require.Equal(t, byte(5), consumertypes.PendingChangesKey()[0])
	i++
	// reserve 6 as deprecated
	i++
	require.Equal(t, byte(7), consumertypes.PreCCVKey()[0])
	i++
	require.Equal(t, byte(8), consumertypes.InitialValSetKey()[0])
	i++
	// reserve 9 as deprecated
	i++
	// reserve 10 as deprecated
	i++
	require.Equal(t, byte(11), consumertypes.HistoricalInfoKeyPrefix()[0])
	i++
	// reserve 12 as deprecated
	i++
	require.Equal(t, byte(13), consumertypes.HeightValsetUpdateIDKeyPrefix()[0])
	i++
	require.Equal(t, byte(14), consumertypes.OutstandingDowntimeKeyPrefix()[0])
	i++
	require.Equal(t, byte(15), consumertypes.PendingDataPacketsV1KeyPrefix()[0])
	i++
	require.Equal(t, byte(16), consumertypes.CrossChainValidatorKeyPrefix()[0])
	i++
	require.Equal(t, byte(17), consumertypes.InitGenesisHeightKey()[0])
	i++
	require.Equal(t, byte(18), consumertypes.StandaloneTransferChannelIDKey()[0])
	i++
	require.Equal(t, byte(19), consumertypes.PrevStandaloneChainKey()[0])
	i++
	require.Equal(t, byte(20), consumertypes.PendingPacketsIndexKey()[0])
	i++
	require.Equal(t, byte(21), consumertypes.SlashRecordKey()[0])
	i++
	require.Equal(t, byte(22), consumertypes.ParametersKey()[0])
	i++

	prefixes := consumertypes.GetAllKeyPrefixes()
	require.Equal(t, len(prefixes), i)
}

func TestNoPrefixOverlap(t *testing.T) {
	keys := getAllFullyDefinedKeys()

	// Make sure that we check all the fully defined keys.
	// All non-deprecated keys should have such a function.
	keyNames := consumertypes.GetAllKeyNames()
	nonDeprecatedKey := []string{}
	for _, name := range keyNames {
		if !strings.Contains(name, "Deprecated") {
			nonDeprecatedKey = append(nonDeprecatedKey, name)
		}
	}
	require.Equal(t, len(nonDeprecatedKey), len(keys))

	seenPrefixes := []byte{}
	for _, key := range keys {
		require.NotContains(t, seenPrefixes, key[0], "Duplicate key prefix: %v", key[0])
		seenPrefixes = append(seenPrefixes, key[0])
	}
}

// getAllFullyDefinedKeys returns instances of byte arrays returned from fully defined key functions.
// Note we only care about checking prefixes here, so parameters into the key functions are arbitrary.
func getAllFullyDefinedKeys() [][]byte {
	return [][]byte{
		consumertypes.PortKey(),
		consumertypes.LastDistributionTransmissionKey(),
		consumertypes.UnbondingTimeKey(),
		consumertypes.ProviderClientIDKey(),
		consumertypes.ProviderChannelIDKey(),
		consumertypes.PendingChangesKey(),
		consumertypes.HistoricalInfoKey(0),
		consumertypes.HeightValsetUpdateIDKey(0),
		consumertypes.OutstandingDowntimeKey(sdk.ConsAddress([]byte{0x05})),
		consumertypes.CrossChainValidatorKey([]byte{0x05}),
		consumertypes.PendingDataPacketsV1Key(0),
		consumertypes.PreCCVKey(),
		consumertypes.InitialValSetKey(),
		consumertypes.InitGenesisHeightKey(),
		consumertypes.StandaloneTransferChannelIDKey(),
		consumertypes.PrevStandaloneChainKey(),
		consumertypes.PendingPacketsIndexKey(),
		consumertypes.SlashRecordKey(),
		consumertypes.ParametersKey(),
	}
}
