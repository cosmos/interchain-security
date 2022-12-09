package types

import (
	time "time"

	sdk "github.com/cosmos/cosmos-sdk/types"
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

	// HistoricalInfoKey is the byte prefix that will store the historical info for a given height
	HistoricalInfoBytePrefix

	// VSCPacketQueueBytePrefix is the byte prefix that will store the ID of each received VSC packet
	// by the maturity time of the VSC packet
	VSCPacketQueueBytePrefix

	// HeightValsetUpdateIDPrefix is the byte prefix that will store the mapping from block height to valset update ID
	HeightValsetUpdateIDBytePrefix

	// OutstandingDowntimePrefix is the byte prefix that will store the validators outstanding downtime by consensus address
	OutstandingDowntimeBytePrefix

	// PendingDataPacketsBytePrefix is the byte prefix for storing
	// a list of data packets that cannot be sent yet to the provider
	// chain either because the CCV channel is not established or
	// because the client is expired
	PendingDataPacketsBytePrefix

	// CrossChainValidatorPrefix is the byte prefix that will store cross-chain validators by consensus address
	CrossChainValidatorBytePrefix
)

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

// VSCPacketQueueKey returns the key for storing the ID of a received VSC packet
// given its maturity time
func VSCPacketQueueKey(timestamp time.Time) []byte {
	timeBz := sdk.FormatTimeBytes(timestamp)
	return append([]byte{VSCPacketQueueBytePrefix}, timeBz...)
}

// HeightValsetUpdateIDKey returns the key to a valset update ID for a given block height
func HeightValsetUpdateIDKey(height uint64) []byte {
	return append([]byte{HeightValsetUpdateIDBytePrefix}, sdk.Uint64ToBigEndian(height)...)
}

// OutstandingDowntimeKey returns the key to a validators' outstanding downtime by consensus address
func OutstandingDowntimeKey(address sdk.ConsAddress) []byte {
	return append([]byte{OutstandingDowntimeBytePrefix}, address.Bytes()...)
}

// CrossChainValidatorKey returns the key to a cross chain validator by consensus address
func CrossChainValidatorKey(addr []byte) []byte {
	return append([]byte{CrossChainValidatorBytePrefix}, addr...)
}

// HistoricalInfoKey returns the key to historical info to a given block height
func HistoricalInfoKey(height int64) []byte {
	return append([]byte{HistoricalInfoBytePrefix}, sdk.Uint64ToBigEndian(uint64(height))...)
}
