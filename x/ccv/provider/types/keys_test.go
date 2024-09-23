package types_test

import (
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	cryptoutil "github.com/cosmos/interchain-security/v6/testutil/crypto"
	providerkeeper "github.com/cosmos/interchain-security/v6/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
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
	require.Equal(t, byte(5), providertypes.ConsumerIdToChannelIdKey("13")[0])
	i++
	require.Equal(t, byte(6), providertypes.ChannelIdToConsumerIdKeyPrefix()[0])
	i++
	require.Equal(t, byte(7), providertypes.ConsumerIdToClientIdKeyPrefix()[0])
	i++
	// reserve 8 as deprecated
	i++
	// reserve 9 as deprecated
	i++
	// reserve 10 as deprecated
	i++
	// reserve 11 as deprecated
	i++
	// reserve 12 as deprecated
	i++
	require.Equal(t, byte(13), providertypes.ValsetUpdateBlockHeightKeyPrefix()[0])
	i++
	require.Equal(t, byte(14), providertypes.ConsumerGenesisKey("13")[0])
	i++
	require.Equal(t, byte(15), providertypes.SlashAcksKey("13")[0])
	i++
	require.Equal(t, byte(16), providertypes.InitChainHeightKey("13")[0])
	i++
	require.Equal(t, byte(17), providertypes.PendingVSCsKey("13")[0])
	i++
	// reserve 18 as deprecated
	i++
	// reserve 19 as deprecated
	i++
	// reserve 20 as deprecated
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
	require.Equal(t, byte(29), providertypes.EquivocationEvidenceMinHeightKey("13")[0])
	i++
	// reserve 30 as deprecated
	i++
	require.Equal(t, byte(31), providertypes.ConsumerValidatorKeyPrefix())
	i++
	require.Equal(t, byte(32), providertypes.OptedInKeyPrefix())
	i++
	// DEPRECATED
	// require.Equal(t, byte(33), providertypes.TopNKey("13")[0])
	i++
	// DEPRECATED
	// require.Equal(t, byte(34), providertypes.ValidatorsPowerCapKey("13")[0])
	i++
	// DEPRECATED
	// require.Equal(t, byte(35), providertypes.ValidatorSetCapKey("13")[0])
	i++
	require.Equal(t, byte(36), providertypes.AllowlistKeyPrefix())
	i++
	require.Equal(t, byte(37), providertypes.DenylistKeyPrefix())
	i++
	require.Equal(t, byte(38), providertypes.ConsumerRewardsAllocationKey("13")[0])
	i++
	require.Equal(t, byte(39), providertypes.ConsumerCommissionRateKeyPrefix())
	i++
	require.Equal(t, byte(40), providertypes.MinimumPowerInTopNKey("13")[0])
	i++
	require.Equal(t, byte(41), providertypes.ConsumerAddrsToPruneV2KeyPrefix())
	i++
	require.Equal(t, byte(42), providertypes.LastProviderConsensusValsPrefix()[0])
	i++
	require.Equal(t, byte(43), providertypes.ConsumerIdKey()[0])
	i++
	require.Equal(t, byte(44), providertypes.ConsumerIdToChainIdKey("13")[0])
	i++
	require.Equal(t, byte(45), providertypes.ConsumerIdToOwnerAddressKey("13")[0])
	i++
	require.Equal(t, byte(46), providertypes.ConsumerIdToMetadataKeyPrefix())
	i++
	require.Equal(t, byte(47), providertypes.ConsumerIdToInitializationParametersKeyPrefix())
	i++
	require.Equal(t, byte(48), providertypes.ConsumerIdToPowerShapingParametersKey("13")[0])
	i++
	require.Equal(t, byte(49), providertypes.ConsumerIdToPhaseKey("13")[0])
	i++
	require.Equal(t, byte(50), providertypes.ConsumerIdToRemovalTimeKeyPrefix())
	i++
	require.Equal(t, byte(51), providertypes.SpawnTimeToConsumerIdsKeyPrefix())
	i++
	require.Equal(t, byte(52), providertypes.RemovalTimeToConsumerIdsKeyPrefix())
	i++
	require.Equal(t, byte(53), providertypes.ClientIdToConsumerIdKey("clientId")[0])
	i++
	require.Equal(t, byte(54), providertypes.ConsumerIdToAllowlistedRewardDenomKey("13")[0])
	i++
	require.Equal(t, byte(55), providertypes.ConsumerRewardsAllocationByDenomKey("13", "denom")[0])
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
		providertypes.ConsumerIdToChannelIdKey("13"),
		providertypes.ChannelToConsumerIdKey("channelID"),
		providertypes.ConsumerIdToClientIdKey("13"),
		providertypes.ValsetUpdateBlockHeightKey(7),
		providertypes.ConsumerGenesisKey("13"),
		providertypes.SlashAcksKey("13"),
		providertypes.InitChainHeightKey("13"),
		providertypes.PendingVSCsKey("13"),
		providertypes.ConsumerValidatorsKey("13", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.ValidatorsByConsumerAddrKey("13", providertypes.NewConsumerConsAddress([]byte{0x05})),
		providertypes.SlashLogKey(providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.ConsumerRewardDenomsKey("uatom"),
		providertypes.EquivocationEvidenceMinHeightKey("13"),
		providertypes.ConsumerValidatorKey("13", providertypes.NewProviderConsAddress([]byte{0x05}).Address.Bytes()),
		providertypes.AllowlistKey("13", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.DenylistKey("13", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.OptedInKey("13", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.ConsumerRewardsAllocationKey("13"),
		providertypes.ConsumerCommissionRateKey("13", providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.MinimumPowerInTopNKey("13"),
		providertypes.ConsumerAddrsToPruneV2Key("13", time.Time{}),
		providerkeeper.GetValidatorKey(providertypes.LastProviderConsensusValsPrefix(), providertypes.NewProviderConsAddress([]byte{0x05})),
		providertypes.ConsumerIdKey(),
		providertypes.ConsumerIdToChainIdKey("13"),
		providertypes.ConsumerIdToOwnerAddressKey("13"),
		providertypes.ConsumerIdToMetadataKey("13"),
		providertypes.ConsumerIdToInitializationParametersKey("13"),
		providertypes.ConsumerIdToPowerShapingParametersKey("13"),
		providertypes.ConsumerIdToPhaseKey("13"),
		providertypes.ConsumerIdToRemovalTimeKey("13"),
		providertypes.SpawnTimeToConsumerIdsKey(time.Time{}),
		providertypes.RemovalTimeToConsumerIdsKey(time.Time{}),
		providertypes.ClientIdToConsumerIdKey("clientId"),
		providertypes.ConsumerIdToAllowlistedRewardDenomKey("13"),
		providertypes.ConsumerRewardsAllocationByDenomKey("13", "denom"),
	}
}

// Tests the construction and parsing of StringIdAndTs keys
func TestStringIdAndTsKeyAndParse(t *testing.T) {
	tests := []struct {
		prefix     byte
		consumerID string
		timestamp  time.Time
	}{
		{prefix: 0x01, consumerID: "1", timestamp: time.Now()},
		{prefix: 0x02, consumerID: "111", timestamp: time.Date(
			2003, 11, 17, 20, 34, 58, 651387237, time.UTC)},
		{prefix: 0x03, consumerID: "2000", timestamp: time.Now().Add(5000 * time.Hour)},
	}

	for _, test := range tests {
		key := providertypes.StringIdAndTsKey(test.prefix, test.consumerID, test.timestamp)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + consumerID length + consumerID + time bytes
		expectedLen := 1 + 8 + len(test.consumerID) + len(sdk.FormatTimeBytes(time.Time{}))
		require.Equal(t, expectedLen, len(key))
		parsedID, parsedTime, err := providertypes.ParseStringIdAndTsKey(test.prefix, key)
		require.Equal(t, test.consumerID, parsedID)
		require.Equal(t, test.timestamp.UTC(), parsedTime.UTC())
		require.NoError(t, err)
	}
}

// Tests the construction and parsing of StringIdAndUintId keys
func TestStringIdAndUintIdAndParse(t *testing.T) {
	tests := []struct {
		prefix     byte
		consumerID string
		uintID     uint64
	}{
		{prefix: 0x01, consumerID: "1", uintID: 1},
		{prefix: 0x02, consumerID: "13", uintID: 2},
		{prefix: 0x03, consumerID: "245", uintID: 3},
	}

	for _, test := range tests {
		key := providertypes.StringIdAndUintIdKey(test.prefix, test.consumerID, test.uintID)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + consumerID length + consumerID + vscId bytes
		expectedLen := 1 + 8 + len(test.consumerID) + 8
		require.Equal(t, expectedLen, len(key))
		parsedChainID, parsedUintID, err := providertypes.ParseStringIdAndUintIdKey(test.prefix, key)
		require.Equal(t, test.consumerID, parsedChainID)
		require.Equal(t, test.uintID, parsedUintID)
		require.NoError(t, err)
	}
}

// Tests the construction and parsing of StringIdAndConsAddr keys
func TestStringIdAndConsAddrAndParse(t *testing.T) {
	cIds := []*cryptoutil.CryptoIdentity{
		cryptoutil.NewCryptoIdentityFromIntSeed(99998),
		cryptoutil.NewCryptoIdentityFromIntSeed(99999),
		cryptoutil.NewCryptoIdentityFromIntSeed(100000),
	}
	pubKey1 := cIds[0].TMCryptoPubKey()
	pubKey2 := cIds[1].TMCryptoPubKey()
	pubKey3 := cIds[2].TMCryptoPubKey()

	tests := []struct {
		prefix     byte
		consumerId string
		addr       sdk.ConsAddress
	}{
		{prefix: 0x01, consumerId: "1", addr: sdk.ConsAddress(pubKey1.Address())},
		{prefix: 0x02, consumerId: "23", addr: sdk.ConsAddress(pubKey2.Address())},
		{prefix: 0x03, consumerId: "456", addr: sdk.ConsAddress(pubKey3.Address())},
	}

	for _, test := range tests {
		key := providertypes.StringIdAndConsAddrKey(test.prefix, test.consumerId, test.addr)
		require.NotEmpty(t, key)
		// Expected bytes = prefix + consumerID length + consumerID + consAddr bytes
		expectedLen := 1 + 8 + len(test.consumerId) + len(test.addr)
		require.Equal(t, expectedLen, len(key))
		parsedID, parsedConsAddr, err := providertypes.ParseStringIdAndConsAddrKey(test.prefix, key)
		require.Equal(t, test.consumerId, parsedID)
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
