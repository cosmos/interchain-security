package types

import (
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"time"
)

type Status int

const (
	// ModuleName defines the CCV parent module name
	ModuleName = "parent"

	// PortID is the default port id that transfer module binds to
	PortID = "parent"

	// StoreKey is the store key string for IBC transfer
	StoreKey = ModuleName

	// RouterKey is the message route for IBC transfer
	RouterKey = ModuleName

	// QuerierRoute is the querier route for IBC transfer
	QuerierRoute = ModuleName

	// ChainToChannelKeyPrefix is the key prefix for storing mapping
	// from chainID to the channel ID that is used to send over validator set changes.
	ChainToChannelKeyPrefix = "chaintochannel"

	// ChannelToChainKeyPrefix is the key prefix for storing mapping
	// from the CCV channel ID to the baby chain ID.
	ChannelToChainKeyPrefix = "channeltochain"

	// ChainToClientKeyPrefix is the key prefix for storing the child chainID for a given child clientid.
	ChainToClientKeyPrefix = "chaintoclient"

	// PendingClientKeyPrefix is the key prefix for storing the pending identified child chain client before the spawn time occurs.
	// The key includes the BigEndian timestamp to allow for efficient chronological iteration
	PendingClientKeyPrefix = "pendingclient"
	// UnbondingDelegationEntryPrefix is the key prefix that stores a record of all the ids of child chains that
	// need to unbond before a given delegation can unbond on this chain.
	UnbondingDelegationEntryPrefix = "ubdeholds"

	// ValidatorSetUpdateIdPrefix is the key prefix that stores the current validator set update id
	ValidatorSetUpdateIdPrefix = "valsetupdateid"

	// UBDEIndexPrefix is for the index for looking up which unbonding delegation entries are waiting for a given
	// child chain to unbond
	UBDEIndexPrefix = "childchaintoubdes"

	//ValsetUpdateBlockHeightPrefix
	ValsetUpdateBlockHeightPrefix = "valsetupdateblockheigt"

	// ChildGenesisStatePrefix stores child genesis state material (consensus state and client state) indexed by child chain id
	ChildGenesisPrefix = "childgenesisstate"
)

var (
	// PortKey defines the key to store the port ID in store
	PortKey = []byte{0x01}
)

// Ouputs a fixed length 32 byte hash for any string
// TODO: use this pattern for all keys
func HashString(x string) []byte {
	hash := sha256.Sum256([]byte(x))
	return hash[:]
}

// Appends a variable number of byte slices together
func AppendMany(byteses ...[]byte) (out []byte) {
	for _, bytes := range byteses {
		out = append(out, bytes...)
	}

	return out
}

// Turns a uint64 to bytes
func Uint64ToBytes(x uint64) []byte {
	bz := make([]byte, 8)
	binary.BigEndian.PutUint64(bz, x)
	return bz
}

// ChainToChannelKey returns the key under which the CCV channel ID will be stored for the given baby chain.
func ChainToChannelKey(chainID string) []byte {
	return []byte(ChainToChannelKeyPrefix + "/" + chainID)
}

// ChannelToChainKey returns the key under which the baby chain ID will be stored for the given channelID.
func ChannelToChainKey(channelID string) []byte {
	return []byte(ChannelToChainKeyPrefix + "/" + channelID)
}

// ChainToClientKey returns the key under which the clientID for the given chainID is stored.
func ChainToClientKey(chainID string) []byte {
	return []byte(fmt.Sprintf("%s/%s", ChainToClientKeyPrefix, chainID))
}

// PendingClientKey returns the key under which a pending identified client is store
func PendingClientKey(timestamp time.Time, chainID string) []byte {
	timeBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(timeBytes, uint64(timestamp.UnixNano()))
	return []byte(fmt.Sprintf("%s/%s/%s", PendingClientKeyPrefix, timeBytes, chainID))
}

func UBDEIndexKey(chainID string, valsetUpdateID uint64) []byte {
	return AppendMany(HashString(UBDEIndexPrefix), HashString(chainID), Uint64ToBytes(valsetUpdateID))
}

func UnbondingDelegationEntryKey(unbondingDelegationEntryID uint64) []byte {
	bz := make([]byte, 8)
	binary.BigEndian.PutUint64(bz, unbondingDelegationEntryID)

	return append([]byte(UnbondingDelegationEntryPrefix), bz...)
}

func ValsetUpdateBlockHeightKey(valsetUpdateId uint64) []byte {
	vuidBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(vuidBytes, valsetUpdateId)
	return append([]byte(ValsetUpdateBlockHeightPrefix), vuidBytes...)
}

func ChildGenesisKey(chainID string) []byte {
	return append(HashString(ChildGenesisPrefix), []byte(chainID)...)
}
