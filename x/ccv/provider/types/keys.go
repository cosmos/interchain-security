package types

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
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

	//PendingStopProposalKeyPrefix is the key prefix for storing the pending identified consumer chain before the stop time occurs.
	// The key includes the BigEndian timestamp to allow for efficient chronological iteration
	PendingStopProposalKeyPrefix = "pendingstopproposal"

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

	// PendingVSCsPrefix is the key prefix that will store pending ValidatorSetChangePacket data
	PendingVSCsPrefix = "pendingvscs"

	// LockUnbondingOnTimeout is the key prefix that will store the consumer chain id which unbonding operations are locked on CCV channel timeout
	LockUnbondingOnTimeoutPrefix = "LockUnbondingOnTimeout"
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

// PendingClientKey returns the key under which a pending identified client is stored
func PendingClientKey(timestamp time.Time, chainID string) []byte {
	timeBz := sdk.FormatTimeBytes(timestamp)
	timeBzL := len(timeBz)
	prefixL := len(PendingClientKeyPrefix)

	bz := make([]byte, prefixL+8+timeBzL+len(chainID))
	// copy the prefix
	copy(bz[:prefixL], PendingClientKeyPrefix)
	// copy the time length
	copy(bz[prefixL:prefixL+8], sdk.Uint64ToBigEndian(uint64(timeBzL)))
	// copy the time bytes
	copy(bz[prefixL+8:prefixL+8+timeBzL], timeBz)
	// copy the chainId
	copy(bz[prefixL+8+timeBzL:], chainID)
	return bz
}

// ParsePendingClientKey returns the time and chain ID for a pending client key or an error if unparseable
func ParsePendingClientKey(bz []byte) (time.Time, string, error) {
	prefixL := len(PendingClientKeyPrefix)
	if prefix := bz[:prefixL]; string(prefix) != PendingClientKeyPrefix {
		return time.Time{}, "", fmt.Errorf("invalid prefix; expected: %X, got: %X", PendingClientKeyPrefix, prefix)
	}

	timeBzL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	timestamp, err := sdk.ParseTimeBytes(bz[prefixL+8 : prefixL+8+int(timeBzL)])
	if err != nil {
		return time.Time{}, "", err
	}

	chainID := string(bz[prefixL+8+int(timeBzL):])
	return timestamp, chainID, nil
}

// PendingStopProposalKey returns the key under which pending consumer chain stop proposals are stored
func PendingStopProposalKey(timestamp time.Time, chainID string) []byte {
	timeBz := sdk.FormatTimeBytes(timestamp)
	timeBzL := len(timeBz)
	prefixL := len([]byte(PendingStopProposalKeyPrefix))

	bz := make([]byte, prefixL+8+timeBzL+len(chainID))
	// copy the prefix
	copy(bz[:prefixL], []byte(PendingStopProposalKeyPrefix))
	// copy the time length
	copy(bz[prefixL:prefixL+8], sdk.Uint64ToBigEndian(uint64(timeBzL)))
	// copy the time bytes
	copy(bz[prefixL+8:prefixL+8+timeBzL], timeBz)
	// copy the chainId
	copy(bz[prefixL+8+timeBzL:], chainID)
	return bz
}

// ParsePendingStopProposalKey returns the time and chain ID for a pending consumer chain stop proposal key or an error if unparseable
func ParsePendingStopProposalKey(bz []byte) (time.Time, string, error) {
	prefixL := len(PendingStopProposalKeyPrefix)
	if prefix := bz[:prefixL]; string(prefix) != PendingStopProposalKeyPrefix {
		return time.Time{}, "", fmt.Errorf("invalid prefix; expected: %X, got: %X", PendingStopProposalKeyPrefix, prefix)
	}

	timeBzL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	timestamp, err := sdk.ParseTimeBytes(bz[prefixL+8 : prefixL+8+int(timeBzL)])
	if err != nil {
		return time.Time{}, "", err
	}

	chainID := string(bz[prefixL+8+int(timeBzL):])
	return timestamp, chainID, nil
}

func UnbondingOpIndexKey(chainID string, valsetUpdateID uint64) []byte {
	return AppendMany(HashString(UnbondingOpIndexPrefix), HashString(chainID), HashString("/"), Uint64ToBytes(valsetUpdateID))
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

// PendingVSCsKey returns the key under which
// pending ValidatorSetChangePacket data is stored for a given chain ID
func PendingVSCsKey(chainID string) []byte {
	return []byte(fmt.Sprintf("%s/%s", PendingVSCsPrefix, chainID))
}

func LockUnbondingOnTimeoutKey(chainID string) []byte {
	return []byte(fmt.Sprintf("%s/%s", LockUnbondingOnTimeoutPrefix, chainID))
}

func ParseUnbondingOpIndexKey(key []byte) (vscID []byte, err error) {
	keySplit := bytes.Split(key, HashString("/"))
	if len(keySplit) != 2 {
		return nil, sdkerrors.Wrapf(
			sdkerrors.ErrLogic, "key provided is incorrect: the key split has incorrect length, expected %d, got %d", 2, len(keySplit),
		)
	}

	return keySplit[1], nil
}
