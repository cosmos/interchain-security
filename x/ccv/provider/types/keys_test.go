package types_test

import (
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	cryptoutil "github.com/cosmos/interchain-security/v5/testutil/crypto"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// Tests that all singular keys, or prefixes to fully resolves keys are non duplicate byte values.
func TestNoDuplicates(t *testing.T) {
	prefixes := providertypes.GetAllKeyPrefixes()
	seen := []byte{}

	for _, prefix := range prefixes {
		require.NotContains(t, seen, prefix, "Duplicate key prefix: %v", prefix)
		seen = append(seen, prefix)
	}
}

// Test that the value of all byte prefixes is preserved
func TestPreserveBytePrefix(t *testing.T) {
	i := 0
	require.Equal(t, uint8(0xFF), providertypes.MustGetKeyPrefix(providertypes.ParametersKeyName))
	i++
	require.Equal(t, uint8(0), providertypes.MustGetKeyPrefix(providertypes.PortKeyName))
	i++
	require.Equal(t, uint8(1), providertypes.MustGetKeyPrefix(providertypes.MaturedUnbondingOpsKeyName))
	i++
	require.Equal(t, uint8(2), providertypes.MustGetKeyPrefix(providertypes.ValidatorSetUpdateIdKeyName))
	i++
	require.Equal(t, uint8(3), providertypes.MustGetKeyPrefix(providertypes.SlashMeterKeyName))
	i++
	require.Equal(t, uint8(4), providertypes.MustGetKeyPrefix(providertypes.SlashMeterReplenishTimeCandidateKeyName))
	i++
	require.Equal(t, uint8(5), providertypes.MustGetKeyPrefix(providertypes.ChainToChannelKeyName))
	i++
	require.Equal(t, uint8(6), providertypes.MustGetKeyPrefix(providertypes.ChannelToChainKeyName))
	i++
	require.Equal(t, uint8(7), providertypes.MustGetKeyPrefix(providertypes.ChainToClientKeyName))
	i++
	require.Equal(t, uint8(8), providertypes.MustGetKeyPrefix(providertypes.InitTimeoutTimestampKeyName))
	i++
	require.Equal(t, uint8(9), providertypes.MustGetKeyPrefix(providertypes.PendingCAPKeyName))
	i++
	require.Equal(t, uint8(10), providertypes.MustGetKeyPrefix(providertypes.PendingCRPKeyName))
	i++
	require.Equal(t, uint8(11), providertypes.MustGetKeyPrefix(providertypes.UnbondingOpKeyName))
	i++
	require.Equal(t, uint8(12), providertypes.MustGetKeyPrefix(providertypes.UnbondingOpIndexKeyName))
	i++
	require.Equal(t, uint8(13), providertypes.MustGetKeyPrefix(providertypes.ValsetUpdateBlockHeightKeyName))
	i++
	require.Equal(t, uint8(14), providertypes.MustGetKeyPrefix(providertypes.ConsumerGenesisKeyName))
	i++
	require.Equal(t, uint8(15), providertypes.MustGetKeyPrefix(providertypes.SlashAcksKeyName))
	i++
	require.Equal(t, uint8(16), providertypes.MustGetKeyPrefix(providertypes.InitChainHeightKeyName))
	i++
	require.Equal(t, uint8(17), providertypes.MustGetKeyPrefix(providertypes.PendingVSCsKeyName))
	i++
	require.Equal(t, uint8(18), providertypes.MustGetKeyPrefix(providertypes.VscSendTimestampKeyName))
	i++
	require.Equal(t, uint8(19), providertypes.MustGetKeyPrefix(providertypes.ThrottledPacketDataSizeKeyName))
	i++
	require.Equal(t, uint8(20), providertypes.MustGetKeyPrefix(providertypes.ThrottledPacketDataKeyName))
	i++
	require.Equal(t, uint8(21), providertypes.MustGetKeyPrefix(providertypes.GlobalSlashEntryKeyName))
	i++
	require.Equal(t, uint8(22), providertypes.MustGetKeyPrefix(providertypes.ConsumerValidatorsKeyName))
	i++
	require.Equal(t, uint8(23), providertypes.MustGetKeyPrefix(providertypes.ValidatorsByConsumerAddrKeyName))
	i++
	require.Equal(t, uint8(24), providertypes.MustGetKeyPrefix(providertypes.KeyAssignmentReplacementsKeyName))
	i++
	require.Equal(t, uint8(25), providertypes.MustGetKeyPrefix(providertypes.ConsumerAddrsToPruneKeyName))
	i++
	require.Equal(t, uint8(26), providertypes.MustGetKeyPrefix(providertypes.SlashLogKeyName))
	i++
	require.Equal(t, uint8(27), providertypes.MustGetKeyPrefix(providertypes.ConsumerRewardDenomsKeyName))
	i++
	require.Equal(t, uint8(28), providertypes.MustGetKeyPrefix(providertypes.VSCMaturedHandledThisBlockKeyName))
	i++
	require.Equal(t, uint8(29), providertypes.MustGetKeyPrefix(providertypes.EquivocationEvidenceMinHeightKeyName))
	i++
	require.Equal(t, uint8(30), providertypes.MustGetKeyPrefix(providertypes.ProposedConsumerChainKeyName))
	i++
	require.Equal(t, uint8(31), providertypes.MustGetKeyPrefix(providertypes.ConsumerValidatorKeyName))
	i++
	require.Equal(t, uint8(32), providertypes.MustGetKeyPrefix(providertypes.OptedInKeyName))
	i++
	require.Equal(t, uint8(33), providertypes.MustGetKeyPrefix(providertypes.TopNKeyName))
	i++
	require.Equal(t, uint8(34), providertypes.MustGetKeyPrefix(providertypes.ValidatorsPowerCapKeyName))
	i++
	require.Equal(t, uint8(35), providertypes.MustGetKeyPrefix(providertypes.ValidatorSetCapKeyName))
	i++
	require.Equal(t, uint8(36), providertypes.MustGetKeyPrefix(providertypes.AllowlistKeyName))
	i++
	require.Equal(t, uint8(37), providertypes.MustGetKeyPrefix(providertypes.DenylistKeyName))
	i++
	require.Equal(t, uint8(38), providertypes.MustGetKeyPrefix(providertypes.ConsumerRewardsAllocationKeyName))
	i++
	require.Equal(t, uint8(39), providertypes.MustGetKeyPrefix(providertypes.ConsumerCommissionRateKeyName))
	i++
	require.Equal(t, uint8(40), providertypes.MustGetKeyPrefix(providertypes.MinimumPowerInTopNKeyName))
	i++
	prefixes := providertypes.GetAllKeyPrefixes()
	require.Equal(t, len(prefixes), i)
}

func TestNoPrefixOverlap(t *testing.T) {
	keys := getAllFullyDefinedKeys()

	// Make sure that we check all the fully defined keys.
	// All non-deprecated keys should have such a function.
	keyNames := providertypes.GetAllKeyNames()
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
		providertypes.ParametersKey(),
		providertypes.PortKey(),
		providertypes.MaturedUnbondingOpsKey(),
		providertypes.ValidatorSetUpdateIdKey(),
		providertypes.SlashMeterKey(),
		providertypes.SlashMeterReplenishTimeCandidateKey(),
		providertypes.ChainToChannelKey("chainID"),
		providertypes.ChannelToChainKey("channelID"),
		providertypes.ChainToClientKey("chainID"),
		providertypes.InitTimeoutTimestampKey("chainID"),
		providertypes.PendingCAPKey(time.Time{}, "chainID"),
		providertypes.PendingCRPKey(time.Time{}, "chainID"),
		providertypes.UnbondingOpKey(7),
		providertypes.UnbondingOpIndexKey("chainID", 7),
		providertypes.ValsetUpdateBlockHeightKey(7),
		providertypes.ConsumerGenesisKey("chainID"),
		providertypes.SlashAcksKey("chainID"),
		providertypes.InitChainHeightKey("chainID"),
		providertypes.PendingVSCsKey("chainID"),
		providertypes.VscSendingTimestampKey("chainID", 8),
		providertypes.ThrottledPacketDataSizeKey("chainID"),
		providertypes.ThrottledPacketDataKey("chainID", 88),
		providertypes.GlobalSlashEntryKey(providertypes.GlobalSlashEntry{}),
		providertypes.ConsumerValidatorsKey("chainID", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.ValidatorsByConsumerAddrKey("chainID", providertypes.NewConsumerConsAddress([]byte{0x05})),
		providertypes.ConsumerAddrsToPruneKey("chainID", 88),
		providertypes.SlashLogKey(providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.VSCMaturedHandledThisBlockKey(),
		providertypes.ConsumerRewardDenomsKey("uatom"),
		providertypes.EquivocationEvidenceMinHeightKey("chainID"),
		providertypes.ProposedConsumerChainKey(1),
		providertypes.ConsumerValidatorKey("chainID", providertypes.NewProviderConsAddress([]byte{0x05}).Address.Bytes()),
		providertypes.TopNKey("chainID"),
		providertypes.ValidatorsPowerCapKey("chainID"),
		providertypes.ValidatorSetCapKey("chainID"),
		providertypes.AllowlistCapKey("chainID", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.DenylistCapKey("chainID", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.OptedInKey("chainID", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.ConsumerRewardsAllocationKey("chainID"),
		providertypes.ConsumerCommissionRateKey("chainID", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.MinimumPowerInTopNKey("chainID"),
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
		key := providertypes.ChainIdAndTsKey(test.prefix, test.chainID, test.timestamp)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + chainID length + chainID + time bytes
		expectedLen := 1 + 8 + len(test.chainID) + len(sdk.FormatTimeBytes(time.Time{}))
		require.Equal(t, expectedLen, len(key))
		parsedID, parsedTime, err := providertypes.ParseChainIdAndTsKey(test.prefix, key)
		require.Equal(t, test.chainID, parsedID)
		require.Equal(t, test.timestamp.UTC(), parsedTime.UTC())
		require.NoError(t, err)
	}
}

// Tests the construction and parsing of ChainIdAndUintId keys
func TestChainIdAndUintIdAndParse(t *testing.T) {
	tests := []struct {
		prefix  byte
		chainID string
		uintID  uint64
	}{
		{prefix: 0x01, chainID: "1", uintID: 1},
		{prefix: 0x02, chainID: "some other ID", uintID: 2},
		{prefix: 0x03, chainID: "some other other chain ID", uintID: 3},
	}

	for _, test := range tests {
		key := providertypes.ChainIdAndUintIdKey(test.prefix, test.chainID, test.uintID)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + chainID length + chainID + vscId bytes
		expectedLen := 1 + 8 + len(test.chainID) + 8
		require.Equal(t, expectedLen, len(key))
		parsedChainID, parsedUintID, err := providertypes.ParseChainIdAndUintIdKey(test.prefix, key)
		require.Equal(t, test.chainID, parsedChainID)
		require.Equal(t, test.uintID, parsedUintID)
		require.NoError(t, err)
	}
}

// Tests the construction and parsing of keys for throttled packet data
func TestThrottledPacketDataKeyAndParse(t *testing.T) {
	tests := []struct {
		consumerChainID string
		ibcSeqNum       uint64
	}{
		{consumerChainID: "some chain id", ibcSeqNum: 45},
		{consumerChainID: "some chain id that is longer", ibcSeqNum: 54038},
		{consumerChainID: "some chain id that is longer-er     ", ibcSeqNum: 9999999999999999999},
	}

	for _, test := range tests {
		key := providertypes.ThrottledPacketDataKey(test.consumerChainID, test.ibcSeqNum)
		require.NotEmpty(t, key)
		// This key should be of len: prefix + chainID length + chainID + ibcSeqNum
		require.Equal(t, 1+8+len(test.consumerChainID)+8, len(key))
		parsedChainID, parsedSeqNum := providertypes.MustParseThrottledPacketDataKey(key)
		require.Equal(t, test.consumerChainID, parsedChainID)
		require.Equal(t, test.ibcSeqNum, parsedSeqNum)
	}

	// Sanity check that two keys with different chain ids but same seq num are different
	key1 := providertypes.ThrottledPacketDataKey("chain-7", 45)
	key2 := providertypes.ThrottledPacketDataKey("chain-8", 45)
	require.NotEqual(t, key1, key2)
}

// Tests the construction and parsing of keys for global slash entries
func TestGlobalSlashEntryKeyAndParse(t *testing.T) {
	now := time.Now()

	providerConsAddrs := []providertypes.ProviderConsAddress{
		cryptoutil.NewCryptoIdentityFromIntSeed(0).ProviderConsAddress(),
		cryptoutil.NewCryptoIdentityFromIntSeed(1).ProviderConsAddress(),
		cryptoutil.NewCryptoIdentityFromIntSeed(2).ProviderConsAddress(),
	}

	entries := []providertypes.GlobalSlashEntry{}
	entries = append(entries, providertypes.NewGlobalSlashEntry(now, "chain-0", 2, providerConsAddrs[0]))
	entries = append(entries, providertypes.NewGlobalSlashEntry(now.Add(2*time.Hour), "chain-7896978", 3, providerConsAddrs[1]))
	entries = append(entries, providertypes.NewGlobalSlashEntry(now.Add(3*time.Hour), "chain-1", 4723894, providerConsAddrs[2]))

	for _, entry := range entries {
		key := providertypes.GlobalSlashEntryKey(entry)
		require.NotEmpty(t, key)
		// This key should be of set length: prefix + 8 + 8 + chainID
		require.Equal(t, 1+8+8+len(entry.ConsumerChainID), len(key))
		parsedRecvTime, parsedChainID, parsedIBCSeqNum := providertypes.MustParseGlobalSlashEntryKey(key)
		require.Equal(t, entry.RecvTime, parsedRecvTime)
		require.Equal(t, entry.ConsumerChainID, parsedChainID)
		require.Equal(t, entry.IbcSeqNum, parsedIBCSeqNum)
	}
}

// Tests the construction and parsing of ChainIdAndConsAddr keys
func TestChainIdAndConsAddrAndParse(t *testing.T) {
	cIds := []*cryptoutil.CryptoIdentity{
		cryptoutil.NewCryptoIdentityFromIntSeed(99998),
		cryptoutil.NewCryptoIdentityFromIntSeed(99999),
		cryptoutil.NewCryptoIdentityFromIntSeed(100000),
	}
	pubKey1 := cIds[0].TMCryptoPubKey()
	pubKey2 := cIds[1].TMCryptoPubKey()
	pubKey3 := cIds[2].TMCryptoPubKey()

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
		key := providertypes.ChainIdAndConsAddrKey(test.prefix, test.chainID, test.addr)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + chainID length + chainID + consAddr bytes
		expectedLen := 1 + 8 + len(test.chainID) + len(test.addr)
		require.Equal(t, expectedLen, len(key))
		parsedID, parsedConsAddr, err := providertypes.ParseChainIdAndConsAddrKey(test.prefix, key)
		require.Equal(t, test.chainID, parsedID)
		require.Equal(t, test.addr, parsedConsAddr)
		require.NoError(t, err)
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
	}

	expectedBytePrefixes := []byte{
		providertypes.MustGetKeyPrefix(providertypes.ChainToChannelKeyName),
		providertypes.MustGetKeyPrefix(providertypes.ChannelToChainKeyName),
		providertypes.MustGetKeyPrefix(providertypes.ChainToClientKeyName),
		providertypes.MustGetKeyPrefix(providertypes.InitTimeoutTimestampKeyName),
		providertypes.MustGetKeyPrefix(providertypes.ConsumerGenesisKeyName),
		providertypes.MustGetKeyPrefix(providertypes.SlashAcksKeyName),
		providertypes.MustGetKeyPrefix(providertypes.InitChainHeightKeyName),
		providertypes.MustGetKeyPrefix(providertypes.PendingVSCsKeyName),
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
		providertypes.MustGetKeyPrefix(providertypes.UnbondingOpKeyName),
		providertypes.MustGetKeyPrefix(providertypes.ValsetUpdateBlockHeightKeyName),
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

func TestParseProposedConsumerChainKey(t *testing.T) {
	tests := []struct {
		chainID    string
		proposalID uint64
	}{
		{chainID: "1", proposalID: 1},
		{chainID: "some other ID", proposalID: 12},
		{chainID: "some other other chain ID", proposalID: 123},
	}

	for _, test := range tests {
		key := providertypes.ProposedConsumerChainKey(test.proposalID)
		pID, err := providertypes.ParseProposedConsumerChainKey(
			providertypes.MustGetKeyPrefix(providertypes.ProposedConsumerChainKeyName), key)
		require.NoError(t, err)
		require.Equal(t, pID, test.proposalID)
	}
}
