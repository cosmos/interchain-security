package types_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
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

	keys := make([][]byte, 32)
	i := 0

	keys[i], i = types.PortKey(), i+1
	keys[i], i = types.MaturedUnbondingOpsKey(), i+1
	keys[i], i = types.ValidatorSetUpdateIdKey(), i+1
	keys[i], i = []byte{types.ChainToChannelBytePrefix}, i+1
	keys[i], i = []byte{types.ChannelToChainBytePrefix}, i+1
	keys[i], i = []byte{types.ChainToClientBytePrefix}, i+1
	keys[i], i = []byte{types.InitTimeoutTimestampBytePrefix}, i+1
	keys[i], i = []byte{types.PendingCAPBytePrefix}, i+1
	keys[i], i = []byte{types.PendingCRPBytePrefix}, i+1
	keys[i], i = []byte{types.UnbondingOpBytePrefix}, i+1
	keys[i], i = []byte{types.UnbondingOpIndexBytePrefix}, i+1
	keys[i], i = []byte{types.ValsetUpdateBlockHeightBytePrefix}, i+1
	keys[i], i = []byte{types.ConsumerGenesisBytePrefix}, i+1
	keys[i], i = []byte{types.SlashAcksBytePrefix}, i+1
	keys[i], i = []byte{types.InitChainHeightBytePrefix}, i+1
	keys[i], i = []byte{types.PendingVSCsBytePrefix}, i+1
	keys[i], i = []byte{types.VscSendTimestampBytePrefix}, i+1
	keys[i], i = []byte{types.LockUnbondingOnTimeoutBytePrefix}, i+1
	keys[i], i = []byte{types.ConsumerValidatorsBytePrefix}, i+1
	keys[i], i = []byte{types.ValidatorsByConsumerAddrBytePrefix}, i+1
	keys[i], i = []byte{types.PendingKeyAssignmentsBytePrefix}, i+1
	keys[i], i = []byte{types.ConsumerValidatorsByVscIDBytePrefix}, i+1

	return keys[:i]
}

// Tests the construction and parsing of TsAndChainId keys
func TestTsAndChainIdKeyAndParse(t *testing.T) {
	tests := []struct {
		prefix    byte
		timestamp time.Time
		chainID   string
	}{
		{prefix: 0x01, timestamp: time.Now(), chainID: "1"},
		{prefix: 0x02, timestamp: time.Date(
			2003, 11, 17, 20, 34, 58, 651387237, time.UTC), chainID: "some other ID"},
		{prefix: 0x03, timestamp: time.Now().Add(5000 * time.Hour), chainID: "some other other chain ID"},
	}

	for _, test := range tests {
		key := types.TsAndChainIdKey(test.prefix, test.timestamp, test.chainID)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + time length + time bytes + length of chainID
		expectedLen := 1 + 8 + len(sdk.FormatTimeBytes(time.Time{})) + len(test.chainID)
		require.Equal(t, expectedLen, len(key))
		parsedTime, parsedID, err := types.ParseTsAndChainIdKey(test.prefix, key)
		require.Equal(t, test.timestamp.UTC(), parsedTime.UTC())
		require.Equal(t, test.chainID, parsedID)
		require.NoError(t, err)
	}
}

// Tests the construction and parsing of ChainIdAndTs keys
func TestChainIdAndTsKeyAndParse(t *testing.T) {
	tests := []struct {
		prefix    byte
		chainID   string
		timestamp time.Time
	}{
		{prefix: 0x01, chainID: "1", timestamp: time.Now()},
		{prefix: 0x02, chainID: "some other ID", timestamp: time.Date(
			2003, 11, 17, 20, 34, 58, 651387237, time.UTC)},
		{prefix: 0x03, chainID: "some other other chain ID", timestamp: time.Now().Add(5000 * time.Hour)},
	}

	for _, test := range tests {
		key := types.ChainIdAndTsKey(test.prefix, test.chainID, test.timestamp)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + chainID length + chainID + time bytes
		expectedLen := 1 + 8 + len(test.chainID) + len(sdk.FormatTimeBytes(time.Time{}))
		require.Equal(t, expectedLen, len(key))
		parsedID, parsedTime, err := types.ParseChainIdAndTsKey(test.prefix, key)
		require.Equal(t, test.chainID, parsedID)
		require.Equal(t, test.timestamp.UTC(), parsedTime.UTC())
		require.NoError(t, err)
	}
}

// Tests the construction and parsing of ChainIdAndVscId keys
func TestChainIdAndVscIdAndParse(t *testing.T) {
	tests := []struct {
		prefix  byte
		chainID string
		vscID   uint64
	}{
		{prefix: 0x01, chainID: "1", vscID: 1},
		{prefix: 0x02, chainID: "some other ID", vscID: 2},
		{prefix: 0x03, chainID: "some other other chain ID", vscID: 3},
	}

	for _, test := range tests {
		key := types.ChainIdAndVscIdKey(test.prefix, test.chainID, test.vscID)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + chainID length + chainID + vscId bytes
		expectedLen := 1 + 8 + len(test.chainID) + 8
		require.Equal(t, expectedLen, len(key))
		parsedID, parsedVscID, err := types.ParseChainIdAndVscIdKey(test.prefix, key)
		require.Equal(t, test.chainID, parsedID)
		require.Equal(t, test.vscID, parsedVscID)
		require.NoError(t, err)
	}
}

// Tests the construction and parsing of ChainIdAndConsAddr keys
func TestChainIdAndConsAddrAndParse(t *testing.T) {
	pubKey1, err := testkeeper.GenPubKey()
	require.NoError(t, err)
	pubKey2, err := testkeeper.GenPubKey()
	require.NoError(t, err)
	pubKey3, err := testkeeper.GenPubKey()
	require.NoError(t, err)

	tests := []struct {
		prefix  byte
		chainID string
		addr    sdk.ConsAddress
	}{
		{prefix: 0x01, chainID: "1", addr: sdk.ConsAddress(pubKey1.Address())},
		{prefix: 0x02, chainID: "some other ID", addr: sdk.ConsAddress(pubKey2.Address())},
		{prefix: 0x03, chainID: "some other other chain ID", addr: sdk.ConsAddress(pubKey3.Address())},
	}

	for _, test := range tests {
		key := types.ChainIdAndConsAddrKey(test.prefix, test.chainID, test.addr)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + chainID length + chainID + consAddr bytes
		expectedLen := 1 + 8 + len(test.chainID) + len(test.addr)
		require.Equal(t, expectedLen, len(key))
		parsedID, parsedConsAddr, err := types.ParseChainIdAndConsAddrKey(test.prefix, key)
		require.Equal(t, test.chainID, parsedID)
		require.Equal(t, test.addr, parsedConsAddr)
		require.NoError(t, err)
	}
}

// Test key packing functions with the format <prefix><stringID>
func TestKeysWithPrefixAndId(t *testing.T) {

	funcs := []func(string) []byte{
		types.ChainToChannelKey,
		types.ChannelToChainKey,
		types.ChainToClientKey,
		types.InitTimeoutTimestampKey,
		types.ConsumerGenesisKey,
		types.SlashAcksKey,
		types.InitChainHeightKey,
		types.PendingVSCsKey,
		types.LockUnbondingOnTimeoutKey,
	}

	expectedBytePrefixes := []byte{
		types.ChainToChannelBytePrefix,
		types.ChannelToChainBytePrefix,
		types.ChainToClientBytePrefix,
		types.InitTimeoutTimestampBytePrefix,
		types.ConsumerGenesisBytePrefix,
		types.SlashAcksBytePrefix,
		types.InitChainHeightBytePrefix,
		types.PendingVSCsBytePrefix,
		types.LockUnbondingOnTimeoutBytePrefix,
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
		types.UnbondingOpKey,
		types.ValsetUpdateBlockHeightKey,
	}

	expectedBytePrefixes := []byte{
		types.UnbondingOpBytePrefix,
		types.ValsetUpdateBlockHeightBytePrefix,
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
