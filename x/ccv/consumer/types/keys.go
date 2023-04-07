package types

import (
	"encoding/binary"
	time "time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	utils "github.com/cosmos/interchain-security/x/ccv/utils"
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
	ConsumerToSendToProviderName = "cons_to_send_to_provider"
)

// Iota generated keys/key prefixes (as a byte), supports 256 possible values
const (
	// PortByteKey defines the byte key to store the port ID in store
	PortByteKey byte = iota

	// LastDistributionTransmissionByteKey defines the byte key to store the last distribution transmission
	LastDistributionTransmissionByteKey

	// UnbondingTimeKeyString is the byte key for storing the unbonding period
	UnbondingTimeByteKey

	// ProviderClientKeyString is the byte key for storing the clientID of the provider client
	ProviderClientByteKey

	// ProviderChannelKeyString is the byte key for storing the channelID of the CCV channel
	ProviderChannelByteKey

	// PendingChangesKeyString is the byte key that will store any pending validator set changes
	// received over CCV channel but not yet flushed over ABCI
	PendingChangesByteKey

	// PendingDataPacketsByteKey is the byte key for storing
	// a list of data packets that cannot be sent yet to the provider
	// chain either because the CCV channel is not established or
	// because the client is expired
	PendingDataPacketsByteKey

	// PreCCVByteKey is the byte to store the consumer is running on democracy staking module without consumer
	PreCCVByteKey

	// InitialValSetByteKey is the byte to store the initial validator set for a consumer
	InitialValSetByteKey

	// LastStandaloneHeightByteKey is the byte that will store last standalone height
	LastStandaloneHeightByteKey

	// HistoricalInfoKey is the byte prefix that will store the historical info for a given height
	HistoricalInfoBytePrefix

	// PacketMaturityTimePrefix is the byte prefix that will store maturity time for each received VSC packet
	PacketMaturityTimeBytePrefix

	// HeightValsetUpdateIDPrefix is the byte prefix that will store the mapping from block height to valset update ID
	HeightValsetUpdateIDBytePrefix

	// OutstandingDowntimePrefix is the byte prefix that will store the validators outstanding downtime by consensus address
	OutstandingDowntimeBytePrefix

	// CrossChainValidatorPrefix is the byte prefix that will store cross-chain validators by consensus address
	CrossChainValidatorBytePrefix

	// SoftOptOutThresholdPowerByteKey is the byte key that will store the power of the largest validator that is
	// allowed to soft opt out
	SoftOptOutThresholdPowerByteKey

	// NOTE: DO NOT ADD NEW BYTE PREFIXES HERE WITHOUT ADDING THEM TO getAllKeyPrefixes() IN keys_test.go
)

//
// Fully defined key func section
//

// PortKey returns the key to the port ID in the store
func PortKey() []byte {
	return []byte{PortByteKey}
}

// LastDistributionTransmissionKey returns the key to the last distribution transmission in the store
func LastDistributionTransmissionKey() []byte {
	return []byte{LastDistributionTransmissionByteKey}
}

// UnbondingTimeKey returns the key for storing the unbonding period
func UnbondingTimeKey() []byte {
	return []byte{UnbondingTimeByteKey}
}

// ProviderClientIDKey returns the key for storing clientID of the provider
func ProviderClientIDKey() []byte {
	return []byte{ProviderClientByteKey}
}

// ProviderChannelKey returns the key for storing channelID of the provider chain
func ProviderChannelKey() []byte {
	return []byte{ProviderChannelByteKey}
}

// PendingChangesKey returns the key for storing pending validator set changes
func PendingChangesKey() []byte {
	return []byte{PendingChangesByteKey}
}

// PendingDataPacketsKey returns the key for storing a list of data packets
// that cannot be sent yet to the provider chain either because the CCV channel
// is not established or because the client is expired.
func PendingDataPacketsKey() []byte {
	return []byte{PendingDataPacketsByteKey}
}

func PreCCVKey() []byte {
	return []byte{PreCCVByteKey}
}

func InitialValSetKey() []byte {
	return []byte{InitialValSetByteKey}
}

func LastStandaloneHeightKey() []byte {
	return []byte{LastStandaloneHeightByteKey}
}

// HistoricalInfoKey returns the key to historical info to a given block height
func HistoricalInfoKey(height int64) []byte {
	hBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(hBytes, uint64(height))
	return append([]byte{HistoricalInfoBytePrefix}, hBytes...)
}

// PacketMaturityTimeKey returns the key for storing the maturity time for a given received VSC packet id
func PacketMaturityTimeKey(vscID uint64, maturityTime time.Time) []byte {
	ts := uint64(maturityTime.UTC().UnixNano())
	return utils.AppendMany(
		// Append the prefix
		[]byte{PacketMaturityTimeBytePrefix},
		// Append the time
		sdk.Uint64ToBigEndian(ts),
		// Append the vscID
		sdk.Uint64ToBigEndian(vscID),
	)
}

// HeightValsetUpdateIDKey returns the key to a valset update ID for a given block height
func HeightValsetUpdateIDKey(height uint64) []byte {
	hBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(hBytes, height)
	return append([]byte{HeightValsetUpdateIDBytePrefix}, hBytes...)
}

// OutstandingDowntimeKey returns the key to a validators' outstanding downtime by consensus address
func OutstandingDowntimeKey(address sdk.ConsAddress) []byte {
	return append([]byte{OutstandingDowntimeBytePrefix}, address.Bytes()...)
}

// CrossChainValidatorKey returns the key to a cross chain validator by consensus address
func CrossChainValidatorKey(addr []byte) []byte {
	return append([]byte{CrossChainValidatorBytePrefix}, addr...)
}

// SoftOptOutThresholdPowerKey returns the key to the power of the largest validator that is allowed to soft opt out
func SoftOptOutThresholdPowerKey() []byte {
	return []byte{SoftOptOutThresholdPowerByteKey}
}

// NOTE: DO	NOT ADD FULLY DEFINED KEY FUNCTIONS WITHOUT ADDING THEM TO getAllFullyDefinedKeys() IN keys_test.go

//
// End of fully defined key func section
//
