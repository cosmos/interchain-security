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
)

// Iota generated keys/byte prefixes (as a byte), supports 256 possible values
const (

	// PortKey defines the key to store the port ID in store
	PortByteKey byte = iota

	// MaturedUnbondingOpsByteKey is the byte key that stores the list of all unbonding operations ids
	// that have matured from a consumer chain perspective,
	// i.e., no longer waiting on the unbonding period to elapse on any consumer chain
	MaturedUnbondingOpsByteKey

	// ValidatorSetUpdateIdByteKey is the byte key that stores the current validator set update id
	ValidatorSetUpdateIdByteKey

	// ChainToChannelBytePrefix is the byte prefix for storing mapping
	// from chainID to the channel ID that is used to send over validator set changes.
	ChainToChannelBytePrefix

	// ChannelToChainBytePrefix is the byte prefix for storing mapping
	// from the CCV channel ID to the consumer chain ID.
	ChannelToChainBytePrefix

	// ChainToClientBytePrefix is the byte prefix for storing the consumer chainID for a given consumer clientid.
	ChainToClientBytePrefix

	// PendingClientBytePrefix is the byte prefix for storing the pending identified consumer chain client before the spawn time occurs.
	// The key includes the BigEndian timestamp to allow for efficient chronological iteration
	PendingClientBytePrefix

	// PendingStopProposalBytePrefix is the byte prefix for storing the pending identified consumer chain before the stop time occurs.
	// The key includes the BigEndian timestamp to allow for efficient chronological iteration
	PendingStopProposalBytePrefix

	// UnbondingOpBytePrefix is the byte prefix that stores a record of all the ids of consumer chains that
	// need to unbond before a given delegation can unbond on this chain.
	UnbondingOpBytePrefix

	// UnbondingOpIndexBytePrefix is byte prefix of the index for looking up which unbonding
	// delegation entries are waiting for a given consumer chain to unbond
	UnbondingOpIndexBytePrefix

	// ValsetUpdateBlockHeightBytePrefix is the byte prefix that will store the mapping from valset update ID to block height
	ValsetUpdateBlockHeightBytePrefix

	// ConsumerGenesisBytePrefix stores consumer genesis state material (consensus state and client state) indexed by consumer chain id
	ConsumerGenesisBytePrefix

	// SlashAcksBytePrefix is the byte prefix that will store consensus address of consumer chain validators successfully slashed on the provider chain
	SlashAcksBytePrefix

	// InitChainHeightBytePrefix is the byte prefix that will store the mapping from a chain id to the corresponding block height on the provider
	// this consumer chain was initialized
	InitChainHeightBytePrefix

	// PendingVSCsBytePrefix is the byte prefix that will store pending ValidatorSetChangePacket data
	PendingVSCsBytePrefix

	// LockUnbondingOnTimeoutBytePrefix is the byte prefix that will store the consumer chain id which unbonding operations are locked on CCV channel timeout
	LockUnbondingOnTimeoutBytePrefix
)

// PortKey returns the key to the port ID in the store
func PortKey() []byte {
	return []byte{PortByteKey}
}

// MaturedUnbondingOpsKey returns the key for storing the list of matured unbonding operations.
func MaturedUnbondingOpsKey() []byte {
	return []byte{MaturedUnbondingOpsByteKey}
}

// ValidatorSetUpdateIdKey is the key that stores the current validator set update id
func ValidatorSetUpdateIdKey() []byte {
	return []byte{ValidatorSetUpdateIdByteKey}
}

// ChainToChannelPrefix is the key prefix for storing mapping
// from chainID to the channel ID that is used to send over validator set changes.
func ChainToChannelPrefix() []byte {
	return []byte{ChainToChannelBytePrefix}
}

// ChannelToChainPrefix is the key prefix for storing mapping
// from the CCV channel ID to the consumer chain ID.
func ChannelToChainPrefix() []byte {
	return []byte{ChannelToChainBytePrefix}
}

// ChainToClientPrefix is the key prefix for storing the consumer chainID for a given consumer clientid.
func ChainToClientPrefix() []byte {
	return []byte{ChainToClientBytePrefix}
}

// PendingClientPrefix is the key prefix for storing the pending identified consumer chain client before the spawn time occurs.
// The key includes the BigEndian timestamp to allow for efficient chronological iteration
func PendingClientPrefix() []byte {
	return []byte{PendingClientBytePrefix}
}

// PendingStopProposalPrefix is the key prefix for storing the pending identified consumer chain before the stop time occurs.
// The key includes the BigEndian timestamp to allow for efficient chronological iteration
func PendingStopProposalPrefix() []byte {
	return []byte{PendingStopProposalBytePrefix}
}

// UnbondingOpPrefix is the key prefix that stores a record of all the ids of consumer chains that
// need to unbond before a given delegation can unbond on this chain.
func UnbondingOpPrefix() []byte {
	return []byte{UnbondingOpBytePrefix}
}

// UnbondingOpIndexPrefix is key prefix of the index for looking up which unbonding
// delegation entries are waiting for a given consumer chain to unbond
func UnbondingOpIndexPrefix() []byte {
	return []byte{UnbondingOpIndexBytePrefix}
}

// ValsetUpdateBlockHeightPrefix is the key prefix that will store the mapping from valset update ID to block height
func ValsetUpdateBlockHeightPrefix() []byte {
	return []byte{ValsetUpdateBlockHeightBytePrefix}
}

// ConsumerGenesisPrefix is the key corresponding to consumer genesis state material
// (consensus state and client state) indexed by consumer chain id
func ConsumerGenesisPrefix() []byte {
	return []byte{ConsumerGenesisBytePrefix}
}

// SlashAcksPrefix is the key prefix that will store consensus address of consumer chain validators successfully slashed on the provider chain
func SlashAcksPrefix() []byte {
	return []byte{SlashAcksBytePrefix}
}

// InitChainHeightPrefix is the key prefix that will store the mapping from a chain id to the corresponding block height on the provider
// this consumer chain was initialized
func InitChainHeightPrefix() []byte {
	return []byte{InitChainHeightBytePrefix}
}

// PendingVSCsPrefix is the key prefix that will store pending ValidatorSetChangePacket data
func PendingVSCsPrefix() []byte {
	return []byte{PendingVSCsBytePrefix}
}

// LockUnbondingOnTimeoutPrefix is the key prefix that will store the consumer chain id which unbonding operations are locked on CCV channel timeout
func LockUnbondingOnTimeoutPrefix() []byte {
	return []byte{LockUnbondingOnTimeoutBytePrefix}
}

// ChainToChannelKey returns the key under which the CCV channel ID will be stored for the given consumer chain.
func ChainToChannelKey(chainID string) []byte {
	return append(ChainToChannelPrefix(), []byte("/"+chainID)...)
}

// ChannelToChainKey returns the key under which the consumer chain ID will be stored for the given channelID.
func ChannelToChainKey(channelID string) []byte {
	return append(ChannelToChainPrefix(), []byte("/"+channelID)...)
}

// ChainToClientKey returns the key under which the clientID for the given chainID is stored.
func ChainToClientKey(chainID string) []byte {
	return append(ChainToClientPrefix(), []byte("/"+chainID)...)
}

// PendingClientKey returns the key under which a pending identified client is stored
func PendingClientKey(timestamp time.Time, chainID string) []byte {
	timeBz := sdk.FormatTimeBytes(timestamp)
	timeBzL := len(timeBz)
	prefixL := len(PendingClientPrefix())

	bz := make([]byte, prefixL+8+timeBzL+len(chainID))
	// copy the prefix
	copy(bz[:prefixL], PendingClientPrefix())
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
	prefixL := len(PendingClientPrefix())
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, PendingClientPrefix()) {
		return time.Time{}, "", fmt.Errorf("invalid prefix; expected: %X, got: %X", PendingClientPrefix(), prefix)
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
	prefixL := len(PendingStopProposalPrefix())

	bz := make([]byte, prefixL+8+timeBzL+len(chainID))
	// copy the prefix
	copy(bz[:prefixL], PendingStopProposalPrefix())
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
	prefixL := len(PendingStopProposalPrefix())
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, PendingStopProposalPrefix()) {
		return time.Time{}, "", fmt.Errorf("invalid prefix; expected: %X, got: %X", PendingStopProposalPrefix(), prefix)
	}

	timeBzL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	timestamp, err := sdk.ParseTimeBytes(bz[prefixL+8 : prefixL+8+int(timeBzL)])
	if err != nil {
		return time.Time{}, "", err
	}

	chainID := string(bz[prefixL+8+int(timeBzL):])
	return timestamp, chainID, nil
}

// UnbondingOpIndexKey returns an unbonding op index key
// Note: chainId is hashed to a fixed length sequence of bytes here to prevent
// injection attack between chainIDs.
func UnbondingOpIndexKey(chainID string, valsetUpdateID uint64) []byte {
	return AppendMany(UnbondingOpIndexPrefix(), HashString(chainID), []byte("/"),
		sdk.Uint64ToBigEndian(valsetUpdateID))
}

// ParseUnbondingOpIndexKey parses an unbonding op index key for VSC ID
func ParseUnbondingOpIndexKey(key []byte) (vscID []byte, err error) {
	keySplit := bytes.Split(key, []byte("/"))
	if len(keySplit) != 2 {
		return nil, sdkerrors.Wrapf(
			sdkerrors.ErrLogic, "key provided is incorrect: the key split has incorrect length, expected %d, got %d", 2, len(keySplit),
		)
	}
	return keySplit[1], nil
}

// UnbondingOpKey returns the key that stores a record of all the ids of consumer chains that
// need to unbond before a given delegation can unbond on this chain
func UnbondingOpKey(id uint64) []byte {
	bz := make([]byte, 8)
	binary.BigEndian.PutUint64(bz, id)
	return append(UnbondingOpPrefix(), bz...)
}

// ValsetUpdateBlockHeightKey returns the key that storing the mapping from valset update ID to block height
func ValsetUpdateBlockHeightKey(valsetUpdateId uint64) []byte {
	vuidBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(vuidBytes, valsetUpdateId)
	return append(ValsetUpdateBlockHeightPrefix(), vuidBytes...)
}

// ConsumerGenesisKey returns the key corresponding to consumer genesis state material
// (consensus state and client state) indexed by consumer chain id
func ConsumerGenesisKey(chainID string) []byte {
	return append(ConsumerGenesisPrefix(), []byte("/"+chainID)...)
}

// SlashAcksKey returns the key under which slashing acks are stored for a given chain ID
func SlashAcksKey(chainID string) []byte {
	return append(SlashAcksPrefix(), []byte("/"+chainID)...)
}

// InitChainHeightKey returns the key under which the block height for a given chain ID is stored
func InitChainHeightKey(chainID string) []byte {
	return append(InitChainHeightPrefix(), []byte("/"+chainID)...)
}

// PendingVSCsKey returns the key under which
// pending ValidatorSetChangePacket data is stored for a given chain ID
func PendingVSCsKey(chainID string) []byte {
	return append(PendingVSCsPrefix(), []byte("/"+chainID)...)
}

// LockUnbondingOnTimeoutKey returns the key that will store the consumer chain id which unbonding operations are locked
// on CCV channel timeout
func LockUnbondingOnTimeoutKey(chainID string) []byte {
	return append(LockUnbondingOnTimeoutPrefix(), []byte("/"+chainID)...)
}

// AppendMany appends a variable number of byte slices together
func AppendMany(byteses ...[]byte) (out []byte) {
	for _, bytes := range byteses {
		out = append(out, bytes...)
	}
	return out
}

// HashString outputs a fixed length 32 byte hash for any string
func HashString(x string) []byte {
	hash := sha256.Sum256([]byte(x))
	return hash[:]
}
