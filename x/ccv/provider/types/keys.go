package types

import (
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"time"
)

type Status int

const (
	// ModuleName defines the CCV provider module name
	ModuleName = "provider"

	// PortID is the default port id that transfer module binds to
	PortID = "provider"

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
	// from the CCV channel ID to the consumer chain ID.
	ChannelToChainKeyPrefix = "channeltochain"

	// ChainToClientKeyPrefix is the key prefix for storing the consumer chainID for a given consumer clientid.
	ChainToClientKeyPrefix = "chaintoclient"

	// PendingClientKeyPrefix is the key prefix for storing the pending identified consumer chain client before the spawn time occurs.
	// The key includes the BigEndian timestamp to allow for efficient chronological iteration
	PendingClientKeyPrefix = "pendingclient"
	// UnbondingOpPrefix is the key prefix that stores a record of all the ids of consumer chains that
	// need to unbond before a given delegation can unbond on this chain.
	UnbondingOpPrefix = "unbondingops"

	// ValidatorSetUpdateIdPrefix is the key prefix that stores the current validator set update id
	ValidatorSetUpdateIdPrefix = "valsetupdateid"

	// UnbondingOpIndexPrefix is for the index for looking up which unbonding delegation entries are waiting for a given
	// consumer chain to unbond
	UnbondingOpIndexPrefix = "consumerchaintounbondingops"

	//ValsetUpdateBlockHeightPrefix is the key prefix that will store the mapping from valset update ID to block height
	ValsetUpdateBlockHeightPrefix = "valsetupdateblockheight"

	// ConsumerGenesisStatePrefix stores consumer genesis state material (consensus state and client state) indexed by consumer chain id
	ConsumerGenesisPrefix = "consumergenesisstate"

	// SlashAcksPrefix is the key prefix that will store consensus address of consumer chain validators successfully slashed on the provider chain
	SlashAcksPrefix = "slashacks"

	// InitChainHeightPrefix is the key prefix that will store the mapping from a chain id to the corresponding block height on the provider
	// this consumer chain was initialized
	InitChainHeightPrefix = "initchainheight"
)

var (
	// PortKey defines the key to store the port ID in store
	PortKey = []byte{0x01}
)

// Ouputs a fixed length 32 byte hash for any string
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

// ChainToChannelKey returns the key under which the CCV channel ID will be stored for the given consumer chain.
func ChainToChannelKey(chainID string) []byte {
	return []byte(ChainToChannelKeyPrefix + "/" + chainID)
}

// ChannelToChainKey returns the key under which the consumer chain ID will be stored for the given channelID.
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

func UnbondingOpIndexKey(chainID string, valsetUpdateID uint64) []byte {
	return AppendMany(HashString(UnbondingOpIndexPrefix), HashString(chainID), Uint64ToBytes(valsetUpdateID))
}

func UnbondingOpKey(id uint64) []byte {
	bz := make([]byte, 8)
	binary.BigEndian.PutUint64(bz, id)

	return append([]byte(UnbondingOpPrefix), bz...)
}

func ValsetUpdateBlockHeightKey(valsetUpdateId uint64) []byte {
	vuidBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(vuidBytes, valsetUpdateId)
	return append([]byte(ValsetUpdateBlockHeightPrefix), vuidBytes...)
}

func ConsumerGenesisKey(chainID string) []byte {
	return append(HashString(ConsumerGenesisPrefix), []byte(chainID)...)
}

// SlashAcksKey returns the key under which slashing acks are stored for a given chain ID
func SlashAcksKey(chainID string) []byte {
	return []byte(fmt.Sprintf("%s/%s", SlashAcksPrefix, chainID))
}

// InitChainHeightKey returns the key under which the block height for a given chain ID is stored
func InitChainHeightKey(chainID string) []byte {
	return []byte(fmt.Sprintf("%s/%s", InitChainHeightPrefix, chainID))
}
