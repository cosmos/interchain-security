package types

import (
	"encoding/binary"
	fmt "fmt"
	"sort"
	time "time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

const (
	// ModuleName defines the CCV consumer module name
	ModuleName = "ccvconsumer"

	// StoreKey is the store key string for IBC consumer
	StoreKey = ModuleName

	// RouterKey is the message route for IBC consumer
	RouterKey = ModuleName

	// QuerierRoute is the querier route for IBC consumer
	QuerierRoute = ModuleName

	// ConsumerRedistributeName the root string for the consumer-redistribution account address
	ConsumerRedistributeName = "cons_redistribute"

	// ConsumerToSendToProviderName is a "buffer" address for outgoing fees to be transferred to the provider chain
	//#nosec G101 -- (false positive) this is not a hardcoded credential
	ConsumerToSendToProviderName = "cons_to_send_to_provider"

	// Names for the store keys.
	// Used for storing the byte prefixes in the constant map.
	// See getKeyPrefixes().

	PortKeyName = "PortKey"

	LastDistributionTransmissionKeyName = "LastDistributionTransmissionKey"

	UnbondingTimeKeyName = "UnbondingTimeKey"

	ProviderClientIDKeyName = "ProviderClientIDKey"

	ProviderChannelIDKeyName = "ProviderChannelIDKey"

	PendingChangesKeyName = "PendingChangesKey"

	DeprecatedPendingDataPacketsV0KeyName = "DeprecatedPendingDataPacketsV0Key"

	PreCCVKeyName = "PreCCVKey"

	InitialValSetKeyName = "InitialValSetKey"

	DeprecatedLastStandaloneHeightKeyName = "DeprecatedLastStandaloneHeightKey"

	DeprecatedSmallestNonOptOutPowerKeyName = "DeprecatedSmallestNonOptOutPowerKey"

	HistoricalInfoKeyName = "HistoricalInfoKey"

	PacketMaturityTimeKeyName = "PacketMaturityTimeKey"

	HeightValsetUpdateIDKeyName = "HeightValsetUpdateIDKey"

	OutstandingDowntimeKeyName = "OutstandingDowntimeKey"

	PendingDataPacketsV1KeyName = "PendingDataPacketsV1Key"

	CrossChainValidatorKeyName = "CrossChainValidatorKey"

	InitGenesisHeightKeyName = "InitGenesisHeightKey"

	StandaloneTransferChannelIDKeyName = "StandaloneTransferChannelIDKey"

	PrevStandaloneChainKeyName = "PrevStandaloneChainKey"

	PendingPacketsIndexKeyName = "PendingPacketsIndexKey"

	SlashRecordKeyName = "SlashRecordKey"

	ParametersKeyName = "ParametersKey"
)

// getKeyPrefixes returns a constant map of all the byte prefixes for existing keys
func getKeyPrefixes() map[string]byte {
	return map[string]byte{
		// PortKey is the key for storing the port ID
		PortKeyName: 0,

		// LastDistributionTransmissionKey is the key for storing the last distribution transmission
		LastDistributionTransmissionKeyName: 1,

		// UnbondingTimeKey is the key for storing the unbonding period
		UnbondingTimeKeyName: 2,

		// ProviderClientIDKey is the key for storing the clientID of the provider client
		ProviderClientIDKeyName: 3,

		// ProviderChannelIDKey is the key for storing the channelID of the CCV channel
		ProviderChannelIDKeyName: 4,

		// PendingChangesKey is the key for storing any pending validator set changes
		// received over CCV channel but not yet flushed over ABCI
		PendingChangesKeyName: 5,

		// NOTE: This prefix is deprecated, but left in place to avoid consumer state migrations
		// [DEPRECATED]
		DeprecatedPendingDataPacketsV0KeyName: 6,

		// PreCCVKey is the key for storing the preCCV flag, which is set to true
		// during the process of a standalone to consumer changeover.
		PreCCVKeyName: 7,

		// InitialValSetKey is the key for storing the initial validator set for a consumer
		InitialValSetKeyName: 8,

		// NOTE: This prefix is deprecated, but left in place to avoid consumer state migrations
		// [DEPRECATED]
		DeprecatedLastStandaloneHeightKeyName: 9,

		// NOTE: This key is deprecated, but left in place to avoid consumer state migrations
		// [DEPRECATED]
		DeprecatedSmallestNonOptOutPowerKeyName: 10,

		// HistoricalInfoKey is the key for storing the historical info for a given height
		HistoricalInfoKeyName: 11,

		// PacketMaturityTimeKey is the key for storing maturity time for each received VSC packet
		PacketMaturityTimeKeyName: 12,

		// HeightValsetUpdateIDKey is the key for storing the mapping from block height to valset update ID
		HeightValsetUpdateIDKeyName: 13,

		// OutstandingDowntimeKey is the key for storing the validators outstanding downtime by consensus address
		OutstandingDowntimeKeyName: 14,

		// PendingDataPacketsV1Key is the key for storing a list of data packets
		// that cannot be sent yet to the provider chain either because the
		// CCV channel is not established or because the client is expired
		PendingDataPacketsV1KeyName: 15,

		// CrossChainValidatorKey is the key for storing cross-chain validators by consensus address
		CrossChainValidatorKeyName: 16,

		// InitGenesisHeightKey is the key for storing the init genesis height
		InitGenesisHeightKeyName: 17,

		// StandaloneTransferChannelIDKey is the key for storing the channelID of transfer channel
		// that existed from a standalone chain changing over to a consumer
		StandaloneTransferChannelIDKeyName: 18,

		// PrevStandaloneChainKey is the key for storing the flag marking whether this chain was previously standalone
		PrevStandaloneChainKeyName: 19,

		// PendingPacketsIndexKey is the key for storing a FIFO queue of pending packets.
		PendingPacketsIndexKeyName: 20,

		// SlashRecordKey is the key for storing the consumer's slash record.
		SlashRecordKeyName: 21,

		// ParametersKey is the key for storing the consumer's parameters.
		ParametersKeyName: 22,

		// NOTE: DO NOT ADD NEW BYTE PREFIXES HERE WITHOUT ADDING THEM TO TestPreserveBytePrefix() IN keys_test.go
	}
}

// mustGetKeyPrefix returns the key prefix for a given key.
// It panics if there is not byte prefix for the index.
func mustGetKeyPrefix(key string) byte {
	keyPrefixes := getKeyPrefixes()
	if prefix, found := keyPrefixes[key]; !found {
		panic(fmt.Sprintf("could not find key prefix for index %s", key))
	} else {
		return prefix
	}
}

// GetAllKeyPrefixes returns all the key prefixes.
// Only used for testing
func GetAllKeyPrefixes() []byte {
	prefixMap := getKeyPrefixes()
	keys := make([]string, 0, len(prefixMap))
	for k := range prefixMap {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	prefixList := make([]byte, 0, len(prefixMap))
	for _, k := range keys {
		prefixList = append(prefixList, prefixMap[k])
	}
	return prefixList
}

// GetAllKeys returns the names of all the keys.
// Only used for testing
func GetAllKeyNames() []string {
	prefixMap := getKeyPrefixes()
	keys := make([]string, 0, len(prefixMap))
	for k := range prefixMap {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

//
// Fully defined key func section
//

// PortKey returns the key for storing the port ID
func PortKey() []byte {
	return []byte{mustGetKeyPrefix(PortKeyName)}
}

// LastDistributionTransmissionKey returns the key for storing the last distribution transmission
func LastDistributionTransmissionKey() []byte {
	return []byte{mustGetKeyPrefix(LastDistributionTransmissionKeyName)}
}

// UnbondingTimeKey returns the key for storing the unbonding period
func UnbondingTimeKey() []byte {
	return []byte{mustGetKeyPrefix(UnbondingTimeKeyName)}
}

// ProviderClientIDKey returns the key for storing clientID of the provider
func ProviderClientIDKey() []byte {
	return []byte{mustGetKeyPrefix(ProviderClientIDKeyName)}
}

// ProviderChannelIDKey returns the key for storing channelID of the provider chain
func ProviderChannelIDKey() []byte {
	return []byte{mustGetKeyPrefix(ProviderChannelIDKeyName)}
}

// PendingChangesKey returns the key for storing pending validator set changes
func PendingChangesKey() []byte {
	return []byte{mustGetKeyPrefix(PendingChangesKeyName)}
}

// PreCCVKey returns the key for storing the preCCV flag, which is set to true
// during the process of a standalone to consumer changeover.
func PreCCVKey() []byte {
	return []byte{mustGetKeyPrefix(PreCCVKeyName)}
}

// InitialValSetKey returns the key for storing the initial validator set for a consumer
func InitialValSetKey() []byte {
	return []byte{mustGetKeyPrefix(InitialValSetKeyName)}
}

// HistoricalInfoKeyPrefix the key prefix for storing the historical info for a given height
func HistoricalInfoKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(HistoricalInfoKeyName)}
}

// HistoricalInfoKey returns the key for storing the historical info for a given height
func HistoricalInfoKey(height int64) []byte {
	hBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(hBytes, uint64(height))
	return append(HistoricalInfoKeyPrefix(), hBytes...)
}

// PacketMaturityTimeKeyPrefix returns the key prefix for storing maturity time for each received VSC packet
func PacketMaturityTimeKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(PacketMaturityTimeKeyName)}
}

// PacketMaturityTimeKey returns the key for storing the maturity time for a given received VSC packet id
func PacketMaturityTimeKey(vscID uint64, maturityTime time.Time) []byte {
	ts := uint64(maturityTime.UTC().UnixNano())
	return ccvtypes.AppendMany(
		// Append the prefix
		PacketMaturityTimeKeyPrefix(),
		// Append the time
		sdk.Uint64ToBigEndian(ts),
		// Append the vscID
		sdk.Uint64ToBigEndian(vscID),
	)
}

// HeightValsetUpdateIDKeyPrefix returns the key for storing a valset update ID for a given block height
func HeightValsetUpdateIDKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(HeightValsetUpdateIDKeyName)}
}

// HeightValsetUpdateIDKey returns the key for storing a valset update ID for a given block height
func HeightValsetUpdateIDKey(height uint64) []byte {
	hBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(hBytes, height)
	return append(HeightValsetUpdateIDKeyPrefix(), hBytes...)
}

// OutstandingDowntimeKeyPrefix returns the key prefix for storing a validators' outstanding downtime by consensus address
func OutstandingDowntimeKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(OutstandingDowntimeKeyName)}
}

// OutstandingDowntimeKey returns the key for storing a validators' outstanding downtime by consensus address
func OutstandingDowntimeKey(address sdk.ConsAddress) []byte {
	return append(OutstandingDowntimeKeyPrefix(), address.Bytes()...)
}

// PendingDataPacketsV1KeyPrefix returns the key prefix for storing a queue of data packets to be sent to the provider.
func PendingDataPacketsV1KeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(PendingDataPacketsV1KeyName)}
}

// PendingDataPacketsKey returns the key for storing a queue of data packets to be sent to the provider.
// Packets in this queue will not be sent on the next endblocker if:
// - the CCV channel is not yet established
// - the client is expired
// - A slash packet is being bounced between consumer and provider (not yet implemented)
func PendingDataPacketsV1Key(idx uint64) []byte {
	return append(PendingDataPacketsV1KeyPrefix(), sdk.Uint64ToBigEndian(idx)...)
}

// CrossChainValidatorKeyPrefix returns the key prefix for storing a cross chain validator by consensus address
func CrossChainValidatorKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(CrossChainValidatorKeyName)}
}

// CrossChainValidatorKey returns the key for storing a cross chain validator by consensus address
func CrossChainValidatorKey(addr []byte) []byte {
	return append(CrossChainValidatorKeyPrefix(), addr...)
}

// InitGenesisHeightKey returns the key for storing the init genesis height
func InitGenesisHeightKey() []byte {
	return []byte{mustGetKeyPrefix(InitGenesisHeightKeyName)}
}

// StandaloneTransferChannelIDKey returns the key for storing the transfer channelID that existed from a standalone chain
// changing over to a consumer
func StandaloneTransferChannelIDKey() []byte {
	return []byte{mustGetKeyPrefix(StandaloneTransferChannelIDKeyName)}
}

// PrevStandaloneChainKey returns the key for storing the flag marking whether this chain was previously standalone
func PrevStandaloneChainKey() []byte {
	return []byte{mustGetKeyPrefix(PrevStandaloneChainKeyName)}
}

// PendingPacketsIndexKey returns the key for storing the FIFO queue of pending packets.
func PendingPacketsIndexKey() []byte {
	return []byte{mustGetKeyPrefix(PendingPacketsIndexKeyName)}
}

// SlashRecordKey returns the key for storing the consumer's slash record.
func SlashRecordKey() []byte {
	return []byte{mustGetKeyPrefix(SlashRecordKeyName)}
}

// ParametersKey returns the key for storing the consumer parameters
func ParametersKey() []byte {
	return []byte{mustGetKeyPrefix(ParametersKeyName)}
}

// NOTE: DO	NOT ADD FULLY DEFINED KEY FUNCTIONS WITHOUT ADDING THEM TO getAllFullyDefinedKeys() IN keys_test.go

//
// End of fully defined key func section
//
