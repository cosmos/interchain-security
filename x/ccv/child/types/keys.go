package types

import (
	"encoding/binary"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/address"
)

const (
	// ModuleName defines the CCV child module name
	ModuleName = "ccvchild"

	// PortID is the default port id that child module binds to
	PortID = "child"

	// StoreKey is the store key string for IBC child
	StoreKey = ModuleName

	// RouterKey is the message route for IBC child
	RouterKey = ModuleName

	// QuerierRoute is the querier route for IBC child
	QuerierRoute = ModuleName

	// ParentClientKeyString is the key for storing the clientID of the parent client
	ParentClientKeyString = "parentclient"

	// ParentChannelKeyString is the key for storing the channelID of the CCV channel
	ParentChannelKeyString = "parentchannel"

	// PendingChangesKeyString is the key that will store any pending validator set changes
	// received over CCV channel but not yet flushed over ABCI
	PendingChangesKeyString = "pendingchanges"

	// UnbondingPacketPrefix is the key prefix that will store the unbonding packet at the given sequence
	UnbondingPacketPrefix = "unbondingpacket"

	// UnbondingTimePrefix is the key prefix that will store unbonding time for each recently received packet.
	UnbondingTimePrefix = "unbondingtime"

	// UnbondingTime is set to 4 weeks
	UnbondingTime = 4 * 7 * 24 * time.Hour

	// HeightValsetUpdateIDPrefix is the key prefix that will store the mapping from block height to valset update ID
	HeightValsetUpdateIDPrefix = "heightvalsetupdateid"

	// OutstandingDowntimePrefix is the key prefix that will store the validators outstanding downtime by consensus address
	OutstandingDowntimePrefix = "outstandingdowntime"

	// CrossChainValidatorPrefix is the key prefix that will store cross-chain validators by consensus address
	CrossChainValidatorPrefix = "crosschainvalidator"

	// ConsumerRedistributeName the root string for the consumer-redistribution account address
	ConsumerRedistributeName = "cons_redistribute"
)

var (
	// PortKey defines the key to store the port ID in store
	PortKey                         = []byte{0x01}
	LastDistributionTransmissionKey = []byte{0x02}
)

// ParentChannelKey returns the key for storing channelID of the parent chain.
func ParentChannelKey() []byte {
	return []byte(ParentChannelKeyString)
}

// ParentClientKey returns the key for storing clientID of the parent
func ParentClientKey() []byte {
	return []byte(ParentClientKeyString)
}

// PendingChangesKey returns the key for storing pending validator set changes
func PendingChangesKey() []byte {
	return []byte(PendingChangesKeyString)
}

// UnbondingPacketKey returns the key for storing unbonding packet for a given received packet sequence
func UnbondingPacketKey(sequence uint64) []byte {
	seqBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(seqBytes, sequence)
	return append([]byte(UnbondingPacketPrefix), seqBytes...)
}

// UnbondingTimeKey returns the key for storing unbonding time for a given received packet sequence
func UnbondingTimeKey(sequence uint64) []byte {
	seqBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(seqBytes, sequence)
	return append([]byte(UnbondingTimePrefix), seqBytes...)
}

func GetSequenceFromUnbondingTimeKey(key []byte) uint64 {
	return binary.BigEndian.Uint64(key[len(UnbondingTimePrefix):])
}

func HeightValsetUpdateIDKey(height uint64) []byte {
	hBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(hBytes, height)
	return append([]byte(HeightValsetUpdateIDPrefix), hBytes...)
}

func OutstandingDowntimeKey(v sdk.ConsAddress) []byte {
	return append([]byte(OutstandingDowntimePrefix), address.MustLengthPrefix(v.Bytes())...)
}

func GetCrossChainValidatorKey(addr []byte) []byte {
	return append([]byte(CrossChainValidatorPrefix), addr...)
}
