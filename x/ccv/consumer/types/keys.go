package types

import (
	"encoding/binary"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/address"
)

const (
	// ModuleName defines the CCV consumer module name
	ModuleName = "ccvconsumer"

	// PortID is the default port id that consumer module binds to
	PortID = "consumer"

	// StoreKey is the store key string for IBC consumer
	StoreKey = ModuleName

	// RouterKey is the message route for IBC consumer
	RouterKey = ModuleName

	// QuerierRoute is the querier route for IBC consumer
	QuerierRoute = ModuleName

	// HistoricalEntries is set to 10000 like the staking module parameter DefaultHistoricalEntries
	HistoricalEntries uint32 = 10000

	// ConsumerRedistributeName the root string for the consumer-redistribution account address
	ConsumerRedistributeName = "cons_redistribute"

	// ConsumerToSendToProviderName is a "buffer" address for outgoing fees to be transferred to the provider chain.
	ConsumerToSendToProviderName = "cons_to_send_to_provider"
)

// Iota generated keys/key prefixes (as a byte), supports 256 possible values.
const (
	// PortByteKey defines the byte key to store the port ID in store
	PortByteKey byte = iota

	// LastDistributionTransmissionByteKey defines the byte key to store the last distribution transmission.
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

	// PacketMaturityTimePrefix is the byte prefix that will store maturity time for each received VSC packet
	PacketMaturityTimeBytePrefix

	// HeightValsetUpdateIDPrefix is the byte prefix that will store the mapping from block height to valset update ID
	HeightValsetUpdateIDBytePrefix

	// OutstandingDowntimePrefix is the byte prefix that will store the validators outstanding downtime by consensus address
	OutstandingDowntimeBytePrefix

	// PendingSlashRequestsPrefix is the byte prefix that will store a list of slash request that must be sent
	// to the provider chain once the CCV channel is established
	PendingSlashRequestsBytePrefix

	// CrossChainValidatorPrefix is the byte prefix that will store cross-chain validators by consensus address
	CrossChainValidatorBytePrefix
)

func PortKey() []byte {
	return []byte{PortByteKey}
}

func LastDistributionTransmissionKey() []byte {
	return []byte{LastDistributionTransmissionByteKey}
}

// UnbondingTimeKey returns the key for storing the unbonding period
func UnbondingTimeKey() []byte {
	return []byte{UnbondingTimeByteKey}
}

// ProviderClientKey returns the key for storing clientID of the provider
func ProviderClientKey() []byte {
	return []byte{ProviderClientByteKey}
}

// ProviderChannelKey returns the key for storing channelID of the provider chain.
func ProviderChannelKey() []byte {
	return []byte{ProviderChannelByteKey}
}

// PendingChangesKey returns the key for storing pending validator set changes
func PendingChangesKey() []byte {
	return []byte{PendingChangesByteKey}
}

func HistoricalInfoPrefix() []byte {
	return []byte{HistoricalInfoBytePrefix}
}

func PacketMaturityTimePrefix() []byte {
	return []byte{PacketMaturityTimeBytePrefix}
}

func HeightValsetUpdateIDPrefix() []byte {
	return []byte{HeightValsetUpdateIDBytePrefix}
}

func OutstandingDowntimePrefix() []byte {
	return []byte{OutstandingDowntimeBytePrefix}
}

func PendingSlashRequestsPrefix() []byte {
	return []byte{PendingSlashRequestsBytePrefix}
}

func CrossChainValidatorPrefix() []byte {
	return []byte{CrossChainValidatorBytePrefix}
}

// PacketMaturityTimeKey returns the key for storing maturity time for a given received VSC packet id
func PacketMaturityTimeKey(id uint64) []byte {
	seqBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(seqBytes, id)
	return append(PacketMaturityTimePrefix(), seqBytes...)
}

func IdFromPacketMaturityTimeKey(key []byte) uint64 {
	return binary.BigEndian.Uint64(key[len(PacketMaturityTimePrefix()):])
}

func HeightValsetUpdateIDKey(height uint64) []byte {
	hBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(hBytes, height)
	return append(HeightValsetUpdateIDPrefix(), hBytes...)
}

func OutstandingDowntimeKey(v sdk.ConsAddress) []byte {
	return append(OutstandingDowntimePrefix(), address.MustLengthPrefix(v.Bytes())...)
}

func CrossChainValidatorKey(addr []byte) []byte {
	return append(CrossChainValidatorPrefix(), addr...)
}

func HistoricalInfoKey(height int64) []byte {
	hBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(hBytes, uint64(height))
	return append(HistoricalInfoPrefix(), hBytes...)
}
