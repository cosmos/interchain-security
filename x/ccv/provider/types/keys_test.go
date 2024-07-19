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
	require.Equal(t, uint8(0xFF), providertypes.ParametersKey()[0])
	i++
	require.Equal(t, uint8(0), providertypes.PortKey()[0])
	i++
	require.Equal(t, uint8(1), providertypes.MaturedUnbondingOpsKey()[0])
	i++
	require.Equal(t, uint8(2), providertypes.ValidatorSetUpdateIdKey()[0])
	i++
	require.Equal(t, uint8(3), providertypes.SlashMeterKey()[0])
	i++
	require.Equal(t, uint8(4), providertypes.SlashMeterReplenishTimeCandidateKey()[0])
	i++
	require.Equal(t, uint8(5), providertypes.ChainToChannelKey("chainID")[0])
	i++
	require.Equal(t, uint8(6), providertypes.ChannelToChainKeyPrefix()[0])
	i++
	require.Equal(t, uint8(7), providertypes.ChainToClientKeyPrefix()[0])
	i++
	require.Equal(t, uint8(8), providertypes.InitTimeoutTimestampKeyPrefix()[0])
	i++
	require.Equal(t, uint8(9), providertypes.PendingCAPKeyPrefix()[0])
	i++
	require.Equal(t, uint8(10), providertypes.PendingCRPKeyPrefix()[0])
	i++
	require.Equal(t, uint8(11), providertypes.UnbondingOpKeyPrefix()[0])
	i++
	require.Equal(t, uint8(12), providertypes.UnbondingOpIndexKeyPrefix())
	i++
	require.Equal(t, uint8(13), providertypes.ValsetUpdateBlockHeightKeyPrefix()[0])
	i++
	require.Equal(t, uint8(14), providertypes.ConsumerGenesisKey("chainID")[0])
	i++
	require.Equal(t, uint8(15), providertypes.SlashAcksKey("chainID")[0])
	i++
	require.Equal(t, uint8(16), providertypes.InitChainHeightKey("chainID")[0])
	i++
	require.Equal(t, uint8(17), providertypes.PendingVSCsKey("chainID")[0])
	i++
	require.Equal(t, uint8(18), providertypes.VscSendingTimestampKeyPrefix())
	i++
	require.Equal(t, uint8(19), providertypes.ThrottledPacketDataSizeKey("chainID")[0])
	i++
	require.Equal(t, uint8(20), providertypes.ThrottledPacketDataKeyPrefix())
	i++
	require.Equal(t, uint8(21), providertypes.GlobalSlashEntryKeyPrefix()[0])
	i++
	require.Equal(t, uint8(22), providertypes.ConsumerValidatorsKeyPrefix())
	i++
	require.Equal(t, uint8(23), providertypes.ValidatorsByConsumerAddrKeyPrefix())
	i++
	// reserve 24 as deprecated
	i++
	require.Equal(t, uint8(25), providertypes.ConsumerAddrsToPruneKeyPrefix())
	i++
	require.Equal(t, uint8(26), providertypes.SlashLogKey(providertypes.NewProviderConsAddress([]byte{0x05}))[0])
	i++
	require.Equal(t, uint8(27), providertypes.ConsumerRewardDenomsKeyPrefix()[0])
	i++
	require.Equal(t, uint8(28), providertypes.VSCMaturedHandledThisBlockKey()[0])
	i++
	require.Equal(t, uint8(29), providertypes.EquivocationEvidenceMinHeightKey("chainID")[0])
	i++
	require.Equal(t, uint8(30), providertypes.ProposedConsumerChainKeyPrefix()[0])
	i++
	require.Equal(t, uint8(31), providertypes.ConsumerValidatorKeyPrefix())
	i++
	require.Equal(t, uint8(32), providertypes.OptedInKeyPrefix())
	i++
	require.Equal(t, uint8(33), providertypes.TopNKey("chainID")[0])
	i++
	require.Equal(t, uint8(34), providertypes.ValidatorsPowerCapKey("chainID")[0])
	i++
	require.Equal(t, uint8(35), providertypes.ValidatorSetCapKey("chainID")[0])
	i++
	require.Equal(t, uint8(36), providertypes.AllowlistKeyPrefix())
	i++
	require.Equal(t, uint8(37), providertypes.DenylistKeyPrefix())
	i++
	require.Equal(t, uint8(38), providertypes.ConsumerRewardsAllocationKey("chainID")[0])
	i++
	require.Equal(t, uint8(39), providertypes.ConsumerCommissionRateKeyPrefix())
	i++
	require.Equal(t, uint8(40), providertypes.MinimumPowerInTopNKey("chainID")[0])
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
		providertypes.AllowlistKey("chainID", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.DenylistKey("chainID", providertypes.NewProviderConsAddress([]byte{0x05})),
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

	tests := []struct {
		stringID string
	}{
		{stringID: "test id 1"},
		{stringID: "2"},
		{stringID: "a longer id to test test test test test"},
	}

	for _, test := range tests {
		for _, function := range funcs {
			key := function(test.stringID)
			require.Equal(t, []byte(test.stringID), key[1:])
		}
	}
}

func TestKeysWithUint64Payload(t *testing.T) {
	funcs := []func(uint64) []byte{
		providertypes.UnbondingOpKey,
		providertypes.ValsetUpdateBlockHeightKey,
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
		for _, function := range funcs {
			key := function(test.integer)
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
		pID, err := providertypes.ParseProposedConsumerChainKey(key)
		require.NoError(t, err)
		require.Equal(t, pID, test.proposalID)
	}
}
