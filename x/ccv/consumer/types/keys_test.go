package types

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"
)

// Tests that all singular keys, or prefixes to fully resolves keys are non duplicate byte values.
func TestNoDuplicates(t *testing.T) {
	prefixes := getAllKeyPrefixes()
	seen := []byte{}

	for _, prefix := range prefixes {
		require.NotContains(t, seen, prefix, "Duplicate key prefix: %v", prefix)
		seen = append(seen, prefix)
	}
}

// Returns all key prefixes to fully resolved keys, any of which should be a single, unique byte.
func getAllKeyPrefixes() []byte {
	return []byte{
		PortByteKey,
		LastDistributionTransmissionByteKey,
		UnbondingTimeByteKey,
		ProviderClientByteKey,
		ProviderChannelByteKey,
		PendingChangesByteKey,
		PendingDataPacketsByteKey,
		PreCCVByteKey,
		InitialValSetByteKey,
		LastStandaloneHeightByteKey,
		SmallestNonOptOutPowerByteKey,
		HistoricalInfoBytePrefix,
		PacketMaturityTimeBytePrefix,
		HeightValsetUpdateIDBytePrefix,
		OutstandingDowntimeBytePrefix,
		PendingDataPacketsBytePrefix,
		CrossChainValidatorBytePrefix,
		InitGenesisHeightByteKey,
		StandaloneTransferChannelIDByteKey,
		PrevStandaloneChainByteKey,
	}
}

func TestNoPrefixOverlap(t *testing.T) {
	keys := getAllFullyDefinedKeys()
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
		PortKey(),
		LastDistributionTransmissionKey(),
		UnbondingTimeKey(),
		ProviderClientIDKey(),
		ProviderChannelKey(),
		PendingChangesKey(),
		// PendingDataPacketsKey() does not use duplicated prefix with value of 0x06
		PreCCVKey(),
		InitialValSetKey(),
		// LastStandaloneHeightKey() is depreciated
		SmallestNonOptOutPowerKey(),
		HistoricalInfoKey(0),
		PacketMaturityTimeKey(0, time.Time{}),
		HeightValsetUpdateIDKey(0),
		OutstandingDowntimeKey([]byte{}),
		PendingDataPacketsKey(),
		CrossChainValidatorKey([]byte{}),
		InitGenesisHeightKey(),
		StandaloneTransferChannelIDKey(),
		PrevStandaloneChainKey(),
	}
}
