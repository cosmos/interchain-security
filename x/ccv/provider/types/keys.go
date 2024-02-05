package types

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
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

	// This address receives rewards from consumer chains
	ConsumerRewardsPool = "consumer_rewards_pool"
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

	// SlashMeterByteKey is the byte key for storing the slash meter
	SlashMeterByteKey

	// SlashMeterReplenishTimeCandidateByteKey is the byte key for storing the slash meter replenish time candidate
	SlashMeterReplenishTimeCandidateByteKey

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
	// need to unbond before a given unbonding operation can unbond on this chain.
	UnbondingOpBytePrefix

	// UnbondingOpIndexBytePrefix is byte prefix of the index for looking up which unbonding
	// operations are waiting for a given consumer chain to unbond
	UnbondingOpIndexBytePrefix

	// ValsetUpdateBlockHeightBytePrefix is the byte prefix that will store the mapping from vscIDs to block heights
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

	// GlobalSlashEntryBytePrefix is the byte prefix storing global slash queue entries
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

	// SlashLogBytePrefix is the byte prefix that will store the mapping from provider address to boolean
	// denoting whether the provider address has committed any double signign infractions
	SlashLogBytePrefix

	// ConsumerRewardDenomsBytePrefix is the byte prefix that will store a list of consumer reward denoms
	ConsumerRewardDenomsBytePrefix

	// VSCMaturedHandledThisBlockBytePrefix is the byte prefix storing the number of vsc matured packets
	// handled in the current block
	VSCMaturedHandledThisBlockBytePrefix

	// EquivocationEvidenceMinHeightBytePrefix is the byte prefix storing the mapping from consumer chain IDs
	// to the minimum height of a valid consumer equivocation evidence
	EquivocationEvidenceMinHeightBytePrefix

	// ProposedConsumerChainByteKey is the byte prefix storing the consumer chainId in consumerAddition gov proposal submitted before voting finishes
	ProposedConsumerChainByteKey

	// TopNBytePrefix is the byte prefix storing the mapping from a consumer chain to the N value of this chain,
	// that corresponds to the N% of the top validators that have to validate this consumer chain
	TopNBytePrefix

	// OptedInBytePrefix is the byte prefix used when storing for each consumer chain all the opted in validators
	OptedInBytePrefix = 31

	// ToBeOptedInBytePrefix is the byte prefix used when storing for each consumer chain the validators that
	// are about to be opted in
	ToBeOptedInBytePrefix = 32

	// ToBeOptedOutBytePrefix is the byte prefix used when storing for each consumer chain the validators that
	// are about to be opted out
	ToBeOptedOutBytePrefix = 33

	// NOTE: DO NOT ADD NEW BYTE PREFIXES HERE WITHOUT ADDING THEM TO getAllKeyPrefixes() IN keys_test.go
)

//
// Fully defined key func section
//

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
	return []byte{SlashMeterByteKey}
}

// SlashMeterReplenishTimeCandidateKey returns the key storing the slash meter replenish time candidate
func SlashMeterReplenishTimeCandidateKey() []byte {
	return []byte{SlashMeterReplenishTimeCandidateByteKey}
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

// PendingCAPKey returns the key under which a pending consumer addition proposal is stored.
// The key has the following format: PendingCAPBytePrefix | timestamp.UnixNano() | chainID
func PendingCAPKey(timestamp time.Time, chainID string) []byte {
	ts := uint64(timestamp.UTC().UnixNano())
	return ccvtypes.AppendMany(
		// Append the prefix
		[]byte{PendingCAPBytePrefix},
		// Append the time
		sdk.Uint64ToBigEndian(ts),
		// Append the chainId
		[]byte(chainID),
	)
}

// PendingCRPKey returns the key under which pending consumer removal proposals are stored.
// The key has the following format: PendingCRPBytePrefix | timestamp.UnixNano() | chainID
func PendingCRPKey(timestamp time.Time, chainID string) []byte {
	ts := uint64(timestamp.UTC().UnixNano())
	return ccvtypes.AppendMany(
		// Append the prefix
		[]byte{PendingCRPBytePrefix},
		// Append the time
		sdk.Uint64ToBigEndian(ts),
		// Append the chainId
		[]byte(chainID),
	)
}

// UnbondingOpKey returns the key that stores a record of all the ids of consumer chains that
// need to unbond before a given unbonding operation can unbond on this chain.
func UnbondingOpKey(id uint64) []byte {
	bz := make([]byte, 8)
	binary.BigEndian.PutUint64(bz, id)
	return append([]byte{UnbondingOpBytePrefix}, bz...)
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

// ThrottledPacketDataSizeKey returns the key storing the size of the throttled packet data queue for a given chain ID
func ThrottledPacketDataSizeKey(consumerChainID string) []byte {
	return append([]byte{ThrottledPacketDataSizeBytePrefix}, []byte(consumerChainID)...)
}

// ThrottledPacketDataKey returns the key storing the throttled packet data queue for a given chain ID and ibc seq num
func ThrottledPacketDataKey(consumerChainID string, ibcSeqNum uint64) []byte {
	return ChainIdAndUintIdKey(ThrottledPacketDataBytePrefix, consumerChainID, ibcSeqNum)
}

// MustParseThrottledPacketDataKey parses a throttled packet data key or panics upon failure
func MustParseThrottledPacketDataKey(key []byte) (string, uint64) {
	chainId, ibcSeqNum, err := ParseThrottledPacketDataKey(key)
	if err != nil {
		panic(fmt.Sprintf("failed to parse throttled packet data key: %s", err.Error()))
	}
	return chainId, ibcSeqNum
}

// ParseThrottledPacketDataKey parses a throttled packet data key
func ParseThrottledPacketDataKey(key []byte) (chainId string, ibcSeqNum uint64, err error) {
	return ParseChainIdAndUintIdKey(ThrottledPacketDataBytePrefix, key)
}

// GlobalSlashEntryKey returns the key for storing a global slash queue entry.
func GlobalSlashEntryKey(entry GlobalSlashEntry) []byte {
	recvTime := uint64(entry.RecvTime.UTC().UnixNano())
	return ccvtypes.AppendMany(
		// Append byte prefix
		[]byte{GlobalSlashEntryBytePrefix},
		// Append time bz
		sdk.Uint64ToBigEndian(recvTime),
		// Append ibc seq num
		sdk.Uint64ToBigEndian(entry.IbcSeqNum),
		// Append consumer chain id
		[]byte(entry.ConsumerChainID),
	)
}

// MustParseGlobalSlashEntryKey returns the received time and chainID for a global slash queue entry key,
// or panics if the key is invalid.
func MustParseGlobalSlashEntryKey(bz []byte) (
	recvTime time.Time, consumerChainID string, ibcSeqNum uint64,
) {
	// Prefix is in first byte
	expectedPrefix := []byte{GlobalSlashEntryBytePrefix}
	if prefix := bz[:1]; !bytes.Equal(prefix, expectedPrefix) {
		panic(fmt.Sprintf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix))
	}

	// 8 bytes for uint64 storing time bytes
	timeBz := sdk.BigEndianToUint64(bz[1:9])
	recvTime = time.Unix(0, int64(timeBz)).UTC()

	// 8 bytes for uint64 storing ibc seq num
	ibcSeqNum = sdk.BigEndianToUint64(bz[9:17])

	// ChainID is stored after 8 byte ibc seq num
	chainID := string(bz[17:])

	return recvTime, chainID, ibcSeqNum
}

// ConsumerValidatorsKey returns the key under which the
// validator assigned keys for every consumer chain are stored
func ConsumerValidatorsKey(chainID string, addr ProviderConsAddress) []byte {
	return ChainIdAndConsAddrKey(ConsumerValidatorsBytePrefix, chainID, addr.ToSdkConsAddr())
}

// ValidatorsByConsumerAddrKey returns the key under which the mapping from validator addresses
// on consumer chains to validator addresses on the provider chain is stored
func ValidatorsByConsumerAddrKey(chainID string, addr ConsumerConsAddress) []byte {
	return ChainIdAndConsAddrKey(ValidatorsByConsumerAddrBytePrefix, chainID, addr.ToSdkConsAddr())
}

// KeyAssignmentReplacementsKey returns the key under which the
// key assignments that need to be replaced in the current block are stored
func KeyAssignmentReplacementsKey(chainID string, addr ProviderConsAddress) []byte {
	return ChainIdAndConsAddrKey(KeyAssignmentReplacementsBytePrefix, chainID, addr.ToSdkConsAddr())
}

// ConsumerAddrsToPruneKey returns the key under which the
// mapping from VSC ids to consumer validators addresses is stored
func ConsumerAddrsToPruneKey(chainID string, vscID uint64) []byte {
	return ChainIdAndUintIdKey(ConsumerAddrsToPruneBytePrefix, chainID, vscID)
}

// SlashLogKey returns the key to a validator's slash log
func SlashLogKey(providerAddr ProviderConsAddress) []byte {
	return append([]byte{SlashLogBytePrefix}, providerAddr.ToSdkConsAddr().Bytes()...)
}

// ConsumerRewardDenomsKey returns the key under which consumer reward denoms are stored
func ConsumerRewardDenomsKey(denom string) []byte {
	return append([]byte{ConsumerRewardDenomsBytePrefix}, []byte(denom)...)
}

// EquivocationEvidenceMinHeightKey returns the key storing the minimum height
// of a valid consumer equivocation evidence for a given consumer chain ID
func EquivocationEvidenceMinHeightKey(consumerChainID string) []byte {
	return append([]byte{EquivocationEvidenceMinHeightBytePrefix}, []byte(consumerChainID)...)
}

// NOTE: DO	NOT ADD FULLY DEFINED KEY FUNCTIONS WITHOUT ADDING THEM TO getAllFullyDefinedKeys() IN keys_test.go

//
// End of fully defined key func section
//

//
// Generic helpers section
//

// ChainIdAndTsKey returns the key with the following format:
// bytePrefix | len(chainID) | chainID | timestamp
func ChainIdAndTsKey(prefix byte, chainID string, timestamp time.Time) []byte {
	partialKey := ChainIdWithLenKey(prefix, chainID)
	timeBz := sdk.FormatTimeBytes(timestamp)
	return ccvtypes.AppendMany(
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
	return ccvtypes.AppendMany(
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
	return ccvtypes.AppendMany(
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
	return ccvtypes.AppendMany(
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

func VSCMaturedHandledThisBlockKey() []byte {
	return []byte{VSCMaturedHandledThisBlockBytePrefix}
}

// ProposedConsumerChainKey returns the key of proposed consumer chainId in consumerAddition gov proposal before voting finishes, the stored key format is prefix|proposalID, value is chainID
func ProposedConsumerChainKey(proposalID uint64) []byte {
	return ccvtypes.AppendMany(
		[]byte{ProposedConsumerChainByteKey},
		sdk.Uint64ToBigEndian(proposalID),
	)
}

// ParseProposedConsumerChainKey get the proposalID in the key
func ParseProposedConsumerChainKey(prefix byte, bz []byte) (uint64, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return 0, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	proposalID := sdk.BigEndianToUint64(bz[prefixL:])

	return proposalID, nil
}

// TopNKey returns the key of consumer chain `chainID`
func TopNKey(chainID string) []byte {
	return ChainIdWithLenKey(TopNBytePrefix, chainID)
}

// OptedInKey returns the key of consumer chain `chainID` and validator with `providerAddr`
func OptedInKey(chainID string, providerAddr ProviderConsAddress) []byte {
	prefix := ChainIdWithLenKey(OptedInBytePrefix, chainID)
	return append(prefix, providerAddr.ToSdkConsAddr().Bytes()...)
}

// ToBeOptedInKey returns the key of consumer chain `chainID` and validator with `providerAddr`
func ToBeOptedInKey(chainID string, providerAddr ProviderConsAddress) []byte {
	prefix := ChainIdWithLenKey(ToBeOptedInBytePrefix, chainID)
	return append(prefix, providerAddr.ToSdkConsAddr().Bytes()...)
}

// ToBeOptedOutKey returns the key of consumer chain `chainID` and validator with `providerAddr`
func ToBeOptedOutKey(chainID string, providerAddr ProviderConsAddress) []byte {
	prefix := ChainIdWithLenKey(ToBeOptedOutBytePrefix, chainID)
	return append(prefix, providerAddr.ToSdkConsAddr().Bytes()...)
}

//
// End of generic helpers section
//
