package types

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
)

type Status int

const (
	// ModuleName defines the CCV provider module name
	ModuleName = "provider"

	// StoreKey is the store key string for IBC transfer
	StoreKey = ModuleName

	// RouterKey is the message route for IBC transfer
	RouterKey = ModuleName

	// QuerierRoute is the querier route for IBC transfer
	QuerierRoute = ModuleName

	// Default validator set update ID
	DefaultValsetUpdateID = 1
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

	// SlashMeterBytePrefix is the byte prefix for storing the slash meter
	SlashMeterBytePrefix

	// LastSlashMeterReplenishTimeBytePrefix is the byte prefix for storing
	// the last time the slash meter was replenished
	LastSlashMeterReplenishTimeBytePrefix

	// ChainToChannelBytePrefix is the byte prefix for storing mapping
	// from chainID to the channel ID that is used to send over validator set changes.
	ChainToChannelBytePrefix

	// ChannelToChainBytePrefix is the byte prefix for storing mapping
	// from the CCV channel ID to the consumer chain ID.
	ChannelToChainBytePrefix

	// ChainToClientBytePrefix is the byte prefix for storing the client ID for a given consumer chainID.
	ChainToClientBytePrefix

	// InitTimeoutTimestampBytePrefix is the byte prefix for storing
	// the init timeout timestamp for a given consumer chainID.
	InitTimeoutTimestampBytePrefix

	// PendingCAPBytePrefix is the byte prefix for storing pending consumer addition proposals before the spawn time occurs.
	// The key includes the BigEndian timestamp to allow for efficient chronological iteration
	PendingCAPBytePrefix

	// PendingCRPBytePrefix is the byte prefix for storing pending consumer removal proposals before the stop time occurs.
	// The key includes the BigEndian timestamp to allow for efficient chronological iteration
	PendingCRPBytePrefix

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

	// VscSendTimestampBytePrefix is the byte prefix for storing
	// the list of VSC sending timestamps for a given consumer chainID.
	VscSendTimestampBytePrefix

	// ThrottledPacketDataSizeBytePrefix is the byte prefix for storing the size of chain-specific throttled packet data queues
	ThrottledPacketDataSizeBytePrefix

	// ThrottledPacketDataBytePrefix is the byte prefix storing throttled packet data
	ThrottledPacketDataBytePrefix

	// PendingSlashPacketEntryBytePrefix is the byte prefix storing global slash queue entries
	GlobalSlashEntryBytePrefix

	// ConsumerValidatorsBytePrefix is the byte prefix that will store the validator assigned keys for every consumer chain
	ConsumerValidatorsBytePrefix

	// ValidatorsByConsumerAddrBytePrefix is the byte prefix that will store the mapping from validator addresses
	// on consumer chains to validator addresses on the provider chain
	ValidatorsByConsumerAddrBytePrefix

	// KeyAssignmentReplacementsBytePrefix is the byte prefix that will store the key assignments that need to be replaced in the current block
	KeyAssignmentReplacementsBytePrefix

	// ConsumerAddrsToPruneBytePrefix is the byte prefix that will store the mapping from VSC ids
	// to consumer validators addresses needed for pruning
	ConsumerAddrsToPruneBytePrefix
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

// SlashMeterKey returns the key storing the slash meter
func SlashMeterKey() []byte {
	return []byte{SlashMeterBytePrefix}
}

// LastSlashMeterReplenishTimeKey returns the key storing the last time the slash meter was replenished
func LastSlashMeterReplenishTimeKey() []byte {
	return []byte{LastSlashMeterReplenishTimeBytePrefix}
}

// ChainToChannelKey returns the key under which the CCV channel ID will be stored for the given consumer chain.
func ChainToChannelKey(chainID string) []byte {
	return append([]byte{ChainToChannelBytePrefix}, []byte(chainID)...)
}

// ChannelToChainKey returns the key under which the consumer chain ID will be stored for the given channelID.
func ChannelToChainKey(channelID string) []byte {
	return append([]byte{ChannelToChainBytePrefix}, []byte(channelID)...)
}

// ChainToClientKey returns the key under which the clientID for the given chainID is stored.
func ChainToClientKey(chainID string) []byte {
	return append([]byte{ChainToClientBytePrefix}, []byte(chainID)...)
}

// InitTimeoutTimestampKey returns the key under which the init timeout timestamp for the given chainID is stored.
func InitTimeoutTimestampKey(chainID string) []byte {
	return append([]byte{InitTimeoutTimestampBytePrefix}, []byte(chainID)...)
}

// PendingCAPKey returns the key under which a pending consumer addition proposal is stored
func PendingCAPKey(timestamp time.Time, chainID string) []byte {
	return TsAndChainIdKey(PendingCAPBytePrefix, timestamp, chainID)
}

// ParsePendingCAPKey returns the time and chain ID for a pending consumer addition proposal key
// or an error if unparsable
func ParsePendingCAPKey(bz []byte) (time.Time, string, error) {
	return ParseTsAndChainIdKey(PendingCAPBytePrefix, bz)
}

// PendingCRPKey returns the key under which pending consumer removal proposals are stored
func PendingCRPKey(timestamp time.Time, chainID string) []byte {
	return TsAndChainIdKey(PendingCRPBytePrefix, timestamp, chainID)
}

// ParsePendingCRPKey returns the time and chain ID for a pending consumer removal proposal key or an error if unparseable
func ParsePendingCRPKey(bz []byte) (time.Time, string, error) {
	return ParseTsAndChainIdKey(PendingCRPBytePrefix, bz)
}

// UnbondingOpIndexKey returns an unbonding op index key
// Note: chainId is hashed to a fixed length sequence of bytes here to prevent
// injection attack between chainIDs.
func UnbondingOpIndexKey(chainID string, vscID uint64) []byte {
	return ChainIdAndUintIdKey(UnbondingOpIndexBytePrefix, chainID, vscID)
}

// ParseUnbondingOpIndexKey parses an unbonding op index key for VSC ID
// Removes the prefix + chainID from index key and returns only the key part.
func ParseUnbondingOpIndexKey(key []byte) (string, uint64, error) {
	return ParseChainIdAndUintIdKey(UnbondingOpIndexBytePrefix, key)
}

// UnbondingOpKey returns the key that stores a record of all the ids of consumer chains that
// need to unbond before a given delegation can unbond on this chain
func UnbondingOpKey(id uint64) []byte {
	bz := make([]byte, 8)
	binary.BigEndian.PutUint64(bz, id)
	return append([]byte{UnbondingOpBytePrefix}, bz...)
}

// ValsetUpdateBlockHeightKey returns the key that storing the mapping from valset update ID to block height
func ValsetUpdateBlockHeightKey(valsetUpdateId uint64) []byte {
	vuidBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(vuidBytes, valsetUpdateId)
	return append([]byte{ValsetUpdateBlockHeightBytePrefix}, vuidBytes...)
}

// ConsumerGenesisKey returns the key corresponding to consumer genesis state material
// (consensus state and client state) indexed by consumer chain id
func ConsumerGenesisKey(chainID string) []byte {
	return append([]byte{ConsumerGenesisBytePrefix}, []byte(chainID)...)
}

// SlashAcksKey returns the key under which slashing acks are stored for a given chain ID
func SlashAcksKey(chainID string) []byte {
	return append([]byte{SlashAcksBytePrefix}, []byte(chainID)...)
}

// InitChainHeightKey returns the key under which the block height for a given chain ID is stored
func InitChainHeightKey(chainID string) []byte {
	return append([]byte{InitChainHeightBytePrefix}, []byte(chainID)...)
}

// PendingVSCsKey returns the key under which
// pending ValidatorSetChangePacket data is stored for a given chain ID
func PendingVSCsKey(chainID string) []byte {
	return append([]byte{PendingVSCsBytePrefix}, []byte(chainID)...)
}

// VscSendingTimestampKey returns the key under which the
// sending timestamp of the VSCPacket with vsc ID is stored
func VscSendingTimestampKey(chainID string, vscID uint64) []byte {
	return ChainIdAndUintIdKey(VscSendTimestampBytePrefix, chainID, vscID)
}

// ParseVscTimeoutTimestampKey returns chain ID and vsc ID
// for a VscSendingTimestampKey or an error if unparsable
func ParseVscSendingTimestampKey(bz []byte) (string, uint64, error) {
	return ParseChainIdAndUintIdKey(VscSendTimestampBytePrefix, bz)
}

// ConsumerValidatorsKey returns the key under which the
// validator assigned keys for every consumer chain are stored
func ConsumerValidatorsKey(chainID string, addr sdk.ConsAddress) []byte {
	return ChainIdAndConsAddrKey(ConsumerValidatorsBytePrefix, chainID, addr)
}

// ValidatorsByConsumerAddrKey returns the key under which the mapping from validator addresses
// on consumer chains to validator addresses on the provider chain is stored
func ValidatorsByConsumerAddrKey(chainID string, addr sdk.ConsAddress) []byte {
	return ChainIdAndConsAddrKey(ValidatorsByConsumerAddrBytePrefix, chainID, addr)
}

// KeyAssignmentReplacementsKey returns the key under which the
// key assignments that need to be replaced in the current block are stored
func KeyAssignmentReplacementsKey(chainID string, addr sdk.ConsAddress) []byte {
	return ChainIdAndConsAddrKey(KeyAssignmentReplacementsBytePrefix, chainID, addr)
}

// ConsumerAddrsToPruneKey returns the key under which the
// mapping from VSC ids to consumer validators addresses is stored
func ConsumerAddrsToPruneKey(chainID string, vscID uint64) []byte {
	return ChainIdAndUintIdKey(ConsumerAddrsToPruneBytePrefix, chainID, vscID)
}

// ThrottledPacketDataSizeKey returns the key storing the size of the throttled packet data queue for a given chain ID
func ThrottledPacketDataSizeKey(consumerChainID string) []byte {
	return append([]byte{ThrottledPacketDataSizeBytePrefix}, []byte(consumerChainID)...)
}

// ThrottledPacketDataKey returns the key storing the throttled packet data queue for a given chain ID and ibc seq num
func ThrottledPacketDataKey(consumerChainID string, ibcSeqNum uint64) []byte {
	return ChainIdAndUintIdKey(ThrottledPacketDataBytePrefix, consumerChainID, ibcSeqNum)
}

// MustParseThrottledPacketDataKey parses a throttled packet data key
// or panics upon failure
func MustParseThrottledPacketDataKey(key []byte) (string, uint64) {
	str, i, err := ParseChainIdAndUintIdKey(ThrottledPacketDataBytePrefix, key)
	if err != nil {
		panic(fmt.Sprintf("failed to parse throttled packet data key: %s", err.Error()))
	}
	return str, i
}

// GlobalSlashEntryKey returns the key for storing a global slash queue entry.
func GlobalSlashEntryKey(entry GlobalSlashEntry) []byte {
	timeBz := sdk.FormatTimeBytes(entry.RecvTime)
	timeBzL := len(timeBz)
	return AppendMany(
		[]byte{GlobalSlashEntryBytePrefix},
		sdk.Uint64ToBigEndian(uint64(timeBzL)),
		timeBz,
		sdk.Uint64ToBigEndian(entry.IbcSeqNum),
		[]byte(entry.ConsumerChainID),
	)
}

// ParseGlobalSlashEntry returns the received time and chainID for a global slash queue entry key.
func ParseGlobalSlashEntryKey(bz []byte) (
	recvTime time.Time, consumerChainID string, ibcSeqNum uint64) {

	// Prefix is in first byte
	expectedPrefix := []byte{GlobalSlashEntryBytePrefix}
	if prefix := bz[:1]; !bytes.Equal(prefix, expectedPrefix) {
		panic(fmt.Sprintf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix))
	}

	// 8 bytes for uint64 storing timestamp length
	timeBzL := sdk.BigEndianToUint64(bz[1:9])
	recvTime, err := sdk.ParseTimeBytes(bz[9 : 9+timeBzL])
	if err != nil {
		panic(err)
	}

	ibcSeqNum = sdk.BigEndianToUint64(bz[9+timeBzL : 9+timeBzL+8])

	// ChainID is stored after 8 byte ibc seq num
	chainID := string(bz[9+timeBzL+8:])

	return recvTime, chainID, ibcSeqNum
}

// AppendMany appends a variable number of byte slices together
func AppendMany(byteses ...[]byte) (out []byte) {
	for _, bytes := range byteses {
		out = append(out, bytes...)
	}
	return out
}

// TsAndChainIdKey returns the key with the following format:
// bytePrefix | len(timestamp) | timestamp | chainID
func TsAndChainIdKey(prefix byte, timestamp time.Time, chainID string) []byte {
	timeBz := sdk.FormatTimeBytes(timestamp)
	timeBzL := len(timeBz)

	return AppendMany(
		// Append the prefix
		[]byte{prefix},
		// Append the time length
		sdk.Uint64ToBigEndian(uint64(timeBzL)),
		// Append the time bytes
		timeBz,
		// Append the chainId
		[]byte(chainID),
	)
}

// ParseTsAndChainIdKey returns the time and chain ID for a TsAndChainId key
func ParseTsAndChainIdKey(prefix byte, bz []byte) (time.Time, string, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return time.Time{}, "", fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}

	timeBzL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	timestamp, err := sdk.ParseTimeBytes(bz[prefixL+8 : prefixL+8+int(timeBzL)])
	if err != nil {
		return time.Time{}, "", err
	}

	chainID := string(bz[prefixL+8+int(timeBzL):])
	return timestamp, chainID, nil
}

// ChainIdAndTsKey returns the key with the following format:
// bytePrefix | len(chainID) | chainID | timestamp
func ChainIdAndTsKey(prefix byte, chainID string, timestamp time.Time) []byte {
	partialKey := ChainIdWithLenKey(prefix, chainID)
	timeBz := sdk.FormatTimeBytes(timestamp)
	return AppendMany(
		// Append the partialKey
		partialKey,
		// Append the time bytes
		timeBz,
	)
}

// ChainIdWithLenKey returns the key with the following format:
// bytePrefix | len(chainID) | chainID
func ChainIdWithLenKey(prefix byte, chainID string) []byte {
	chainIdL := len(chainID)
	return AppendMany(
		// Append the prefix
		[]byte{prefix},
		// Append the chainID length
		sdk.Uint64ToBigEndian(uint64(chainIdL)),
		// Append the chainID
		[]byte(chainID),
	)
}

// ParseChainIdAndTsKey returns the chain ID and time for a ChainIdAndTs key
func ParseChainIdAndTsKey(prefix byte, bz []byte) (string, time.Time, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return "", time.Time{}, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	chainIdL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	chainID := string(bz[prefixL+8 : prefixL+8+int(chainIdL)])
	timestamp, err := sdk.ParseTimeBytes(bz[prefixL+8+int(chainIdL):])
	if err != nil {
		return "", time.Time{}, err
	}
	return chainID, timestamp, nil
}

// ChainIdAndUintIdKey returns the key with the following format:
// bytePrefix | len(chainID) | chainID | uint64(ID)
func ChainIdAndUintIdKey(prefix byte, chainID string, uintId uint64) []byte {
	partialKey := ChainIdWithLenKey(prefix, chainID)
	return AppendMany(
		// Append the partialKey
		partialKey,
		// Append the uint id bytes
		sdk.Uint64ToBigEndian(uintId),
	)
}

// ParseChainIdAndUintIdKey returns the chain ID and uint ID for a ChainIdAndUintId key
func ParseChainIdAndUintIdKey(prefix byte, bz []byte) (string, uint64, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return "", 0, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	chainIdL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	chainID := string(bz[prefixL+8 : prefixL+8+int(chainIdL)])
	uintID := sdk.BigEndianToUint64(bz[prefixL+8+int(chainIdL):])
	return chainID, uintID, nil
}

// ChainIdAndConsAddrKey returns the key with the following format:
// bytePrefix | len(chainID) | chainID | ConsAddress
func ChainIdAndConsAddrKey(prefix byte, chainID string, addr sdk.ConsAddress) []byte {
	partialKey := ChainIdWithLenKey(prefix, chainID)
	return AppendMany(
		// Append the partialKey
		partialKey,
		// Append the addr bytes
		addr,
	)
}

// ParseChainIdAndConsAddrKey returns the chain ID and ConsAddress for a ChainIdAndConsAddrKey key
func ParseChainIdAndConsAddrKey(prefix byte, bz []byte) (string, sdk.ConsAddress, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return "", nil, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	chainIdL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	chainID := string(bz[prefixL+8 : prefixL+8+int(chainIdL)])
	addr := bz[prefixL+8+int(chainIdL):]
	return chainID, addr, nil
}
