package types_test

import (
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	cryptoutil "github.com/cosmos/interchain-security/v5/testutil/crypto"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
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
	require.Equal(t, byte(0xFF), providertypes.ParametersKey()[0])
	i++
	require.Equal(t, byte(0), providertypes.PortKey()[0])
	i++
	// reserve 1 as deprecated
	i++
	require.Equal(t, byte(2), providertypes.ValidatorSetUpdateIdKey()[0])
	i++
	require.Equal(t, byte(3), providertypes.SlashMeterKey()[0])
	i++
	require.Equal(t, byte(4), providertypes.SlashMeterReplenishTimeCandidateKey()[0])
	i++
	require.Equal(t, uint8(5), providertypes.ConsumerIdToChannelIdKey("chainID")[0])
	i++
	require.Equal(t, uint8(6), providertypes.ChannelIdToConsumerIdKeyPrefix()[0])
	i++
	require.Equal(t, uint8(7), providertypes.ConsumerIdToClientIdKeyPrefix()[0])
	i++
	// reserve 8 as deprecated
	i++
	require.Equal(t, byte(9), providertypes.PendingCAPKeyPrefix()[0])
	i++
	require.Equal(t, byte(10), providertypes.PendingCRPKeyPrefix()[0])
	i++
	// reserve 11 as deprecated
	i++
	// reserve 12 as deprecated
	i++
	require.Equal(t, byte(13), providertypes.ValsetUpdateBlockHeightKeyPrefix()[0])
	i++
	require.Equal(t, byte(14), providertypes.ConsumerGenesisKey("chainID")[0])
	i++
	require.Equal(t, byte(15), providertypes.SlashAcksKey("chainID")[0])
	i++
	require.Equal(t, byte(16), providertypes.InitChainHeightKey("chainID")[0])
	i++
	require.Equal(t, byte(17), providertypes.PendingVSCsKey("chainID")[0])
	i++
	// reserve 18 as deprecated
	i++
	require.Equal(t, byte(19), providertypes.ThrottledPacketDataSizeKey("chainID")[0])
	i++
	require.Equal(t, byte(20), providertypes.ThrottledPacketDataKeyPrefix())
	i++
	// DEPRECATED
	// require.Equal(t, uint8(21), providertypes.GlobalSlashEntryKeyPrefix()[0])
	i++
	require.Equal(t, byte(22), providertypes.ConsumerValidatorsKeyPrefix())
	i++
	require.Equal(t, byte(23), providertypes.ValidatorsByConsumerAddrKeyPrefix())
	i++
	// reserve 24 as deprecated
	i++
	// reserve 25 as deprecated
	i++
	require.Equal(t, byte(26), providertypes.SlashLogKey(providertypes.NewProviderConsAddress([]byte{0x05}))[0])
	i++
	require.Equal(t, byte(27), providertypes.ConsumerRewardDenomsKeyPrefix()[0])
	i++
	// reserve 28 as deprecated
	i++
	require.Equal(t, byte(29), providertypes.EquivocationEvidenceMinHeightKey("chainID")[0])
	i++
	require.Equal(t, byte(30), providertypes.ProposedConsumerChainKeyPrefix()[0])
	i++
	require.Equal(t, byte(31), providertypes.ConsumerValidatorKeyPrefix())
	i++
	require.Equal(t, byte(32), providertypes.OptedInKeyPrefix())
	i++
	require.Equal(t, byte(33), providertypes.TopNKey("chainID")[0])
	i++
	require.Equal(t, byte(34), providertypes.ValidatorsPowerCapKey("chainID")[0])
	i++
	require.Equal(t, byte(35), providertypes.ValidatorSetCapKey("chainID")[0])
	i++
	require.Equal(t, byte(36), providertypes.AllowlistKeyPrefix())
	i++
	require.Equal(t, byte(37), providertypes.DenylistKeyPrefix())
	i++
	require.Equal(t, byte(38), providertypes.ConsumerRewardsAllocationKey("chainID")[0])
	i++
	require.Equal(t, byte(39), providertypes.ConsumerCommissionRateKeyPrefix())
	i++
	require.Equal(t, byte(40), providertypes.MinimumPowerInTopNKey("chainID")[0])
	i++
	require.Equal(t, byte(41), providertypes.ConsumerAddrsToPruneV2KeyPrefix())
	i++
	require.Equal(t, byte(42), providertypes.LastProviderConsensusValsPrefix()[0])
	i++
	require.Equal(t, byte(43), providertypes.MinStakeKey("chainID")[0])
	i++
	require.Equal(t, byte(44), providertypes.AllowInactiveValidatorsKey("chainID")[0])
	i++
	require.Equal(t, uint8(45), providertypes.ConsumerIdKey()[0])
	i++
	require.Equal(t, uint8(46), providertypes.ConsumerIdToChainIdKey("consumerId")[0])
	i++
	require.Equal(t, uint8(47), providertypes.ConsumerIdToRegistrationRecordKey("consumerId")[0])
	i++
	require.Equal(t, uint8(48), providertypes.ConsumerIdToInitializationRecordKey("consumerId")[0])
	i++
	require.Equal(t, uint8(49), providertypes.ConsumerIdToOwnerAddressKey("consumerId")[0])
	i++
	require.Equal(t, uint8(47), providertypes.ConsumerIdToPhaseKey("consumerId")[0])
	i++
	require.Equal(t, uint8(48), providertypes.ClientIdToConsumerIdKey("clientId")[0])
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
		providertypes.ValidatorSetUpdateIdKey(),
		providertypes.SlashMeterKey(),
		providertypes.SlashMeterReplenishTimeCandidateKey(),
		providertypes.ConsumerIdToChannelIdKey("chainID"),
		providertypes.ChannelToConsumerIdKey("channelID"),
		providertypes.ConsumerIdToClientIdKey("chainID"),
		providertypes.PendingCAPKey(time.Time{}, "chainID"),
		providertypes.PendingCRPKey(time.Time{}, "chainID"),
		providertypes.ValsetUpdateBlockHeightKey(7),
		providertypes.ConsumerGenesisKey("chainID"),
		providertypes.SlashAcksKey("chainID"),
		providertypes.InitChainHeightKey("chainID"),
		providertypes.PendingVSCsKey("chainID"),
		providertypes.ThrottledPacketDataSizeKey("chainID"),
		providertypes.ThrottledPacketDataKey("chainID", 88),
		providertypes.ConsumerValidatorsKey("chainID", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.ValidatorsByConsumerAddrKey("chainID", providertypes.NewConsumerConsAddress([]byte{0x05})),
		providertypes.SlashLogKey(providertypes.NewProviderConsAddress([]byte{0x05})),
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
		providertypes.ConsumerAddrsToPruneV2Key("chainID", time.Time{}),
		providertypes.MinStakeKey("chainID"),
		providertypes.AllowInactiveValidatorsKey("chainID"),
		providerkeeper.GetValidatorKey(types.LastProviderConsensusValsPrefix(), providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.ConsumerIdKey(),
		providertypes.ConsumerIdToChainIdKey("consumerId"),
		providertypes.ConsumerIdToRegistrationRecordKey("consumerId"),
		providertypes.ConsumerIdToInitializationRecordKey("consumerId"),
		providertypes.ConsumerIdToOwnerAddressKey("consumerId"),
		providertypes.ConsumerIdToPhaseKey("consumerId"),
		providertypes.ClientIdToConsumerIdKey("clientId"),
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
		key := providertypes.ConsumerIdAndConsAddrKey(test.prefix, test.chainID, test.addr)
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
		providertypes.ConsumerIdToChannelIdKey,
		providertypes.ChannelToConsumerIdKey,
		providertypes.ConsumerIdToClientIdKey,
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
