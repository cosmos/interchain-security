package types_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/tendermint/crypto/ed25519"
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

	keys := make([][]byte, 32)
	i := 0

	keys[i], i = providertypes.PortKey(), i+1
	keys[i], i = providertypes.MaturedUnbondingOpsKey(), i+1
	keys[i], i = providertypes.ValidatorSetUpdateIdKey(), i+1
	keys[i], i = providertypes.SlashMeterKey(), i+1
	keys[i], i = providertypes.LastSlashMeterReplenishTimeKey(), i+1
	keys[i], i = []byte{providertypes.ChainToChannelBytePrefix}, i+1
	keys[i], i = []byte{providertypes.ChannelToChainBytePrefix}, i+1
	keys[i], i = []byte{providertypes.ChainToClientBytePrefix}, i+1
	keys[i], i = []byte{providertypes.InitTimeoutTimestampBytePrefix}, i+1
	keys[i], i = []byte{providertypes.PendingCAPBytePrefix}, i+1
	keys[i], i = []byte{providertypes.PendingCRPBytePrefix}, i+1
	keys[i], i = []byte{providertypes.UnbondingOpBytePrefix}, i+1
	keys[i], i = []byte{providertypes.UnbondingOpIndexBytePrefix}, i+1
	keys[i], i = []byte{providertypes.ValsetUpdateBlockHeightBytePrefix}, i+1
	keys[i], i = []byte{providertypes.ConsumerGenesisBytePrefix}, i+1
	keys[i], i = []byte{providertypes.SlashAcksBytePrefix}, i+1
	keys[i], i = []byte{providertypes.InitChainHeightBytePrefix}, i+1
	keys[i], i = []byte{providertypes.PendingVSCsBytePrefix}, i+1
	keys[i], i = []byte{providertypes.LockUnbondingOnTimeoutBytePrefix}, i+1
	keys[i] = []byte{providertypes.PendingSlashPacketEntryBytePrefix}

	return keys[:i]
}

// Tests the construction and parsing of keys for storing pending consumer addition proposals
func TestPendingCAPKeyAndParse(t *testing.T) {
	tests := []struct {
		timestamp time.Time
		chainID   string
	}{
		{timestamp: time.Now(), chainID: "1"},
		{timestamp: time.Date(
			2003, 11, 17, 20, 34, 58, 651387237, time.UTC), chainID: "some other ID"},
		{timestamp: time.Now().Add(5000 * time.Hour), chainID: "some other other chain ID"},
	}

	for _, test := range tests {
		key := providertypes.PendingCAPKey(test.timestamp, test.chainID)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + time length + time bytes + length of chainID
		expectedBytes := 1 + 8 + len(sdk.FormatTimeBytes(time.Time{})) + len(test.chainID)
		require.Equal(t, expectedBytes, len(key))
		parsedTime, parsedID, err := providertypes.ParsePendingCAPKey(key)
		require.Equal(t, test.timestamp.UTC(), parsedTime.UTC())
		require.Equal(t, test.chainID, parsedID)
		require.NoError(t, err)
	}
}

// Tests the construction and parsing of keys for storing pending consumer removal proposals
func TestPendingCRPKeyAndParse(t *testing.T) {
	tests := []struct {
		timestamp time.Time
		chainID   string
	}{
		{timestamp: time.Now(), chainID: "5"},
		{timestamp: time.Date(
			2003, 11, 17, 20, 34, 58, 651387237, time.UTC), chainID: "some other ID"},
		{timestamp: time.Now().Add(5000 * time.Hour), chainID: "some other other chain ID"},
	}

	for _, test := range tests {
		key := providertypes.PendingCRPKey(test.timestamp, test.chainID)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + time length + time bytes + length of chainID
		expectedBytes := 1 + 8 + len(sdk.FormatTimeBytes(time.Time{})) + len(test.chainID)
		require.Equal(t, expectedBytes, len(key))
		parsedTime, parsedID, err := providertypes.ParsePendingCRPKey(key)
		require.Equal(t, test.timestamp.UTC(), parsedTime.UTC())
		require.Equal(t, test.chainID, parsedID)
		require.NoError(t, err)
	}
}

func TestUnbondingOpIndexKeyAndParse(t *testing.T) {
	tests := []struct {
		chainID        string
		valsetUpdateID uint64
	}{
		{chainID: " some chain id", valsetUpdateID: 45},
		{chainID: " some chain id that is longer", valsetUpdateID: 54038},
		{chainID: " some chain id that is longer-er     ", valsetUpdateID: 9999999999999999999},
		{chainID: "2", valsetUpdateID: 0},
	}

	for _, test := range tests {
		key := providertypes.UnbondingOpIndexKey(test.chainID, test.valsetUpdateID)
		require.NotEmpty(t, key)
		// This key should be of set length: prefix + hashed chain ID + uint64
		require.Equal(t, 1+32+8, len(key))
		parsedVSCID, err := providertypes.ParseUnbondingOpIndexKey(key)
		require.NotEmpty(t, parsedVSCID)
		asUint64 := sdk.BigEndianToUint64(parsedVSCID)
		require.Equal(t, test.valsetUpdateID, asUint64)
		require.NoError(t, err)
	}
}

// Tests the construction and parsing of keys for pending slash packet entries
func TestPendingSlashPacketEntryKeyAndParse(t *testing.T) {
	now := time.Now()
	entries := []providertypes.SlashPacketEntry{}
	entries = append(entries, providertypes.NewSlashPacketEntry(now, "chain-0", ed25519.GenPrivKey().PubKey().Address()))
	entries = append(entries, providertypes.NewSlashPacketEntry(now.Add(2*time.Hour), "chain-7896978", ed25519.GenPrivKey().PubKey().Address()))
	entries = append(entries, providertypes.NewSlashPacketEntry(now.Add(3*time.Hour), "chain-1", ed25519.GenPrivKey().PubKey().Address()))

	for _, entry := range entries {
		key := providertypes.PendingSlashPacketEntryKey(entry)
		require.NotEmpty(t, key)
		timeBzL := len(sdk.FormatTimeBytes(entry.RecvTime))
		// This key should be of set length: prefix + 8 + timeBzL + hashed valAddr + chainID
		require.Equal(t, 1+8+timeBzL+32+len(entry.ConsumerChainID), len(key))
		parsedRecvTime, parsedChainID := providertypes.ParsePendingSlashPacketEntryKey(key)
		require.Equal(t, entry.RecvTime, parsedRecvTime)
		require.Equal(t, entry.ConsumerChainID, parsedChainID)
	}
}

// Test key packing functions with the format <prefix><stringID>
func TestKeysWithPrefixAndId(t *testing.T) {

	funcs := []func(string) []byte{
		providertypes.ChainToChannelKey,
		providertypes.ChannelToChainKey,
		providertypes.ChainToClientKey,
		providertypes.InitTimeoutTimestampKey,
		providertypes.ConsumerGenesisKey,
		providertypes.SlashAcksKey,
		providertypes.InitChainHeightKey,
		providertypes.PendingVSCsKey,
		providertypes.LockUnbondingOnTimeoutKey,
	}

	expectedBytePrefixes := []byte{
		providertypes.ChainToChannelBytePrefix,
		providertypes.ChannelToChainBytePrefix,
		providertypes.ChainToClientBytePrefix,
		providertypes.InitTimeoutTimestampBytePrefix,
		providertypes.ConsumerGenesisBytePrefix,
		providertypes.SlashAcksBytePrefix,
		providertypes.InitChainHeightBytePrefix,
		providertypes.PendingVSCsBytePrefix,
		providertypes.LockUnbondingOnTimeoutBytePrefix,
	}

	tests := []struct {
		stringID string
	}{
		{stringID: "test id 1"},
		{stringID: "2"},
		{stringID: "a longer id to test test test test test"},
	}

	for _, test := range tests {
		for funcIdx, function := range funcs {
			key := function(test.stringID)
			require.Equal(t, expectedBytePrefixes[funcIdx], key[0])
			require.Equal(t, []byte(test.stringID), key[1:])
		}
	}
}

func TestKeysWithUint64Payload(t *testing.T) {

	funcs := []func(uint64) []byte{
		providertypes.UnbondingOpKey,
		providertypes.ValsetUpdateBlockHeightKey,
	}

	expectedBytePrefixes := []byte{
		providertypes.UnbondingOpBytePrefix,
		providertypes.ValsetUpdateBlockHeightBytePrefix,
	}

	tests := []struct {
		integer uint64
	}{
		{integer: 0},
		{integer: 25},
		{integer: 3472843},
		{integer: 8503458034859305834},
	}

	for _, test := range tests {
		for funcIdx, function := range funcs {
			key := function(test.integer)
			require.Equal(t, expectedBytePrefixes[funcIdx], key[0])
			require.Equal(t, sdk.Uint64ToBigEndian(test.integer), key[1:])
		}
	}
}
