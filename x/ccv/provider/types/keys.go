package types

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
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

// getKeyPrefixes returns a constant map of all the byte prefixes for existing keys
func getKeyPrefixes() map[string]byte {
	return map[string]byte{
		// ParametersKey is the is the key for storing provider's parameters.
		// note that this was set to the max uint8 type value 0xFF in order to protect
		// from using the ICS v5.0.0 provider module by mistake
		"ParametersKey": byte(0xFF),

		// PortKey defines the key to store the port ID in store
		"PortKey": 0,

		// MaturedUnbondingOpsKey is the key that stores the list of all unbonding operations ids
		// that have matured from a consumer chain perspective,
		// i.e., no longer waiting on the unbonding period to elapse on any consumer chain
		"MaturedUnbondingOpsKey": 1,

		// ValidatorSetUpdateIdKey is the key that stores the current validator set update id
		"ValidatorSetUpdateIdKey": 2,

		// SlashMeterKey is the key for storing the slash meter
		"SlashMeterKey": 3,

		// SlashMeterReplenishTimeCandidateKey is the key for storing the slash meter replenish time candidate
		"SlashMeterReplenishTimeCandidateKey": 4,

		// ChainToChannelKey is the key for storing mapping
		// from chainID to the channel ID that is used to send over validator set changes.
		"ChainToChannelKey": 5,

		// ChannelToChainKey is the key for storing mapping
		// from the CCV channel ID to the consumer chain ID.
		"ChannelToChainKey": 6,

		// ChainToClientKey is the key for storing the client ID for a given consumer chainID.
		"ChainToClientKey": 7,

		// InitTimeoutTimestampKey is the key for storing
		// the init timeout timestamp for a given consumer chainID.
		"InitTimeoutTimestampKey": 8,

		// PendingCAPKey is the key for storing pending consumer addition proposals before the spawn time occurs.
		// The key includes the BigEndian timestamp to allow for efficient chronological iteration
		"PendingCAPKey": 9,

		// PendingCRPKey is the key for storing pending consumer removal proposals before the stop time occurs.
		// The key includes the BigEndian timestamp to allow for efficient chronological iteration
		"PendingCRPKey": 10,

		// UnbondingOpKey is the key that stores a record of all the ids of consumer chains that
		// need to unbond before a given unbonding operation can unbond on this chain.
		"UnbondingOpKey": 11,

		// UnbondingOpIndexKey is key of the index for looking up which unbonding
		// operations are waiting for a given consumer chain to unbond
		"UnbondingOpIndexKey": 12,

		// ValsetUpdateBlockHeightKey is the key for storing the mapping from vscIDs to block heights
		"ValsetUpdateBlockHeightKey": 13,

		// ConsumerGenesisKey stores consumer genesis state material (consensus state and client state) indexed by consumer chain id
		"ConsumerGenesisKey": 14,

		// SlashAcksKey is the key for storing consensus address of consumer chain validators successfully slashed on the provider chain
		"SlashAcksKey": 15,

		// InitChainHeightKey is the key for storing the mapping from a chain id to the corresponding block height on the provider
		// this consumer chain was initialized
		"InitChainHeightKey": 16,

		// PendingVSCsKey is the key for storing pending ValidatorSetChangePacket data
		"PendingVSCsKey": 17,

		// VscSendTimestampKey is the key for storing
		// the list of VSC sending timestamps for a given consumer chainID.
		"VscSendTimestampKey": 18,

		// ThrottledPacketDataSizeKey is the key for storing the size of chain-specific throttled packet data queues
		"ThrottledPacketDataSizeKey": 19,

		// ThrottledPacketDataKey is the key for storing throttled packet data
		"ThrottledPacketDataKey": 20,

		// GlobalSlashEntryKey is the key for storing global slash queue entries
		"GlobalSlashEntryKey": 21,

		// ConsumerValidatorsKey is the key for storing the validator assigned keys for every consumer chain
		"ConsumerValidatorsKey": 22,

		// ValidatorsByConsumerAddrKey is the key for storing the mapping from validator addresses
		// on consumer chains to validator addresses on the provider chain
		"ValidatorsByConsumerAddrKey": 23,

		// DeprecatedKeyAssignmentReplacementsKey was the key used to store the key assignments that needed to be replaced in the current block
		// NOTE: This prefix is deprecated, but left in place to avoid consumer state migrations
		// [DEPRECATED]
		"DeprecatedKeyAssignmentReplacementsKey": 24,

		// ConsumerAddrsToPruneKey is the key for storing the mapping from VSC ids
		// to consumer validators addresses needed for pruning
		"ConsumerAddrsToPruneKey": 25,

		// SlashLogKey is the key for storing the mapping from provider address to boolean
		// denoting whether the provider address has committed any double signign infractions
		"SlashLogKey": 26,

		// ConsumerRewardDenomsKey is the key for storing a list of consumer reward denoms
		"ConsumerRewardDenomsKey": 27,

		// VSCMaturedHandledThisBlockKey is the key for storing the number of vsc matured packets
		// handled in the current block
		"VSCMaturedHandledThisBlockKey": 28,

		// EquivocationEvidenceMinHeightKey is the key for storing the mapping from consumer chain IDs
		// to the minimum height of a valid consumer equivocation evidence
		"EquivocationEvidenceMinHeightKey": 29,

		// ProposedConsumerChainKey is the key for storing the consumer chainId in consumerAddition gov proposal submitted before voting finishes
		"ProposedConsumerChainKey": 30,

		// ConsumerValidatorKey is the key for storing for each consumer chain all the consumer
		// validators in this epoch that are validating the consumer chain
		"ConsumerValidatorKey": 31,

		// OptedInKey is the key for storing whether a validator is opted in to validate on a consumer chain
		"OptedInKey": 32,

		// TopNKey is the key for storing the mapping from a consumer chain to the N value of this chain,
		// that corresponds to the N% of the top validators that have to validate this consumer chain
		"TopNKey": 33,

		// ValidatorsPowerCapKey is the key for  storing the mapping from a consumer chain to the power-cap value of this chain,
		// that corresponds to p% such that no validator can have more than p% of the voting power on the consumer chain.
		// Operates on a best-effort basis.
		"ValidatorsPowerCapKey": 34,

		// ValidatorSetCapKey is the key for storing the mapping from a consumer chain to the validator-set cap value
		// of this chain.
		"ValidatorSetCapKey": 35,

		// AllowlistKey is the key for storing the mapping from a consumer chain to the set of validators that are
		// allowlisted.
		"AllowlistKey": 36,

		// DenylistKey is the key for storing the mapping from a consumer chain to the set of validators that are
		// denylisted.
		"DenylistKey": 37,

		// ConsumerRewardsAllocationKey is the key for storing for each consumer the ICS rewards
		// allocated to the consumer rewards pool
		"ConsumerRewardsAllocationKey": 38,

		// ConsumerCommissionRateKey is the key for storing the commission rate
		// per validator per consumer chain
		"ConsumerCommissionRateKey": 39,

		// MinimumPowerInTopNKey is the key for storing the
		// minimum power required to be in the top N per consumer chain.
		"MinimumPowerInTopNKey": 40,

		// NOTE: DO NOT ADD NEW BYTE PREFIXES HERE WITHOUT ADDING THEM TO getAllKeyPrefixes() IN keys_test.go
	}
}

// MustGetKeyPrefix returns the key prefix for a given index.
// It panics if there is not byte prefix for the index.
func MustGetKeyPrefix(index string) byte {
	keyPrefixes := getKeyPrefixes()
	if prefix, found := keyPrefixes[index]; !found {
		panic(fmt.Sprintf("could not find key prefix for index %s", index))
	} else {
		return prefix
	}
}

// GetAllKeyPrefixes returns all the key prefixes.
// Only used for testing
func GetAllKeyPrefixes() []byte {
	prefixMap := getKeyPrefixes()
	prefixList := make([]byte, 0, len(prefixMap))
	for _, prefix := range prefixMap {
		prefixList = append(prefixList, prefix)
	}
	return prefixList
}

//
// Fully defined key func section
//

// ParametersKey returns the key for the parameters of the provider module in the store
func ParametersKey() []byte {
	return []byte{MustGetKeyPrefix("ParametersKey")}
}

// PortKey returns the key to the port ID in the store
func PortKey() []byte {
	return []byte{MustGetKeyPrefix("PortKey")}
}

// MaturedUnbondingOpsKey returns the key for storing the list of matured unbonding operations.
func MaturedUnbondingOpsKey() []byte {
	return []byte{MustGetKeyPrefix("MaturedUnbondingOpsKey")}
}

// ValidatorSetUpdateIdKey is the key that stores the current validator set update id
func ValidatorSetUpdateIdKey() []byte {
	return []byte{MustGetKeyPrefix("ValidatorSetUpdateIdKey")}
}

// SlashMeterKey returns the key storing the slash meter
func SlashMeterKey() []byte {
	return []byte{MustGetKeyPrefix("SlashMeterKey")}
}

// SlashMeterReplenishTimeCandidateKey returns the key storing the slash meter replenish time candidate
func SlashMeterReplenishTimeCandidateKey() []byte {
	return []byte{MustGetKeyPrefix("SlashMeterReplenishTimeCandidateKey")}
}

// ChainToChannelKey returns the key under which the CCV channel ID will be stored for the given consumer chain.
func ChainToChannelKey(chainID string) []byte {
	return append([]byte{MustGetKeyPrefix("ChainToChannelKey")}, []byte(chainID)...)
}

// ChannelToChainKey returns the key under which the consumer chain ID will be stored for the given channelID.
func ChannelToChainKey(channelID string) []byte {
	return append([]byte{MustGetKeyPrefix("ChannelToChainKey")}, []byte(channelID)...)

}

// ChainToClientKey returns the key under which the clientID for the given chainID is stored.
func ChainToClientKey(chainID string) []byte {
	return append([]byte{MustGetKeyPrefix("ChainToClientKey")}, []byte(chainID)...)
}

// InitTimeoutTimestampKey returns the key under which the init timeout timestamp for the given chainID is stored.
func InitTimeoutTimestampKey(chainID string) []byte {
	return append([]byte{MustGetKeyPrefix("InitTimeoutTimestampKey")}, []byte(chainID)...)
}

// PendingCAPKey returns the key under which a pending consumer addition proposal is stored.
// The key has the following format: PendingCAPKey | timestamp.UnixNano() | chainID
func PendingCAPKey(timestamp time.Time, chainID string) []byte {
	ts := uint64(timestamp.UTC().UnixNano())
	return ccvtypes.AppendMany(
		// Append the prefix
		[]byte{MustGetKeyPrefix("PendingCAPKey")},
		// Append the time
		sdk.Uint64ToBigEndian(ts),
		// Append the chainId
		[]byte(chainID),
	)
}

// PendingCRPKey returns the key under which pending consumer removal proposals are stored.
// The key has the following format: PendingCRPKey | timestamp.UnixNano() | chainID
func PendingCRPKey(timestamp time.Time, chainID string) []byte {
	ts := uint64(timestamp.UTC().UnixNano())
	return ccvtypes.AppendMany(
		// Append the prefix
		[]byte{MustGetKeyPrefix("PendingCRPKey")},
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
	return append([]byte{MustGetKeyPrefix("UnbondingOpKey")}, bz...)
}

// UnbondingOpIndexKey returns an unbonding op index key
// Note: chainId is hashed to a fixed length sequence of bytes here to prevent
// injection attack between chainIDs.
func UnbondingOpIndexKey(chainID string, vscID uint64) []byte {
	return ChainIdAndUintIdKey(MustGetKeyPrefix("UnbondingOpIndexKey"), chainID, vscID)
}

// ParseUnbondingOpIndexKey parses an unbonding op index key for VSC ID
// Removes the prefix + chainID from index key and returns only the key part.
func ParseUnbondingOpIndexKey(key []byte) (string, uint64, error) {
	return ParseChainIdAndUintIdKey(MustGetKeyPrefix("UnbondingOpIndexKey"), key)
}

// ValsetUpdateBlockHeightKey returns the key that storing the mapping from valset update ID to block height
func ValsetUpdateBlockHeightKey(valsetUpdateId uint64) []byte {
	vuidBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(vuidBytes, valsetUpdateId)
	return append([]byte{MustGetKeyPrefix("ValsetUpdateBlockHeightKey")}, vuidBytes...)
}

// ConsumerGenesisKey returns the key corresponding to consumer genesis state material
// (consensus state and client state) indexed by consumer chain id
func ConsumerGenesisKey(chainID string) []byte {
	return append([]byte{MustGetKeyPrefix("ConsumerGenesisKey")}, []byte(chainID)...)
}

// SlashAcksKey returns the key under which slashing acks are stored for a given chain ID
func SlashAcksKey(chainID string) []byte {
	return append([]byte{MustGetKeyPrefix("SlashAcksKey")}, []byte(chainID)...)
}

// InitChainHeightKey returns the key under which the block height for a given chain ID is stored
func InitChainHeightKey(chainID string) []byte {
	return append([]byte{MustGetKeyPrefix("InitChainHeightKey")}, []byte(chainID)...)
}

// PendingVSCsKey returns the key under which
// pending ValidatorSetChangePacket data is stored for a given chain ID
func PendingVSCsKey(chainID string) []byte {
	return append([]byte{MustGetKeyPrefix("PendingVSCsKey")}, []byte(chainID)...)
}

// VscSendingTimestampKey returns the key under which the
// sending timestamp of the VSCPacket with vsc ID is stored
func VscSendingTimestampKey(chainID string, vscID uint64) []byte {
	return ChainIdAndUintIdKey(MustGetKeyPrefix("VscSendTimestampKey"), chainID, vscID)
}

// ParseVscTimeoutTimestampKey returns chain ID and vsc ID
// for a VscSendingTimestampKey or an error if unparsable
func ParseVscSendingTimestampKey(bz []byte) (string, uint64, error) {
	return ParseChainIdAndUintIdKey(MustGetKeyPrefix("VscSendTimestampKey"), bz)
}

// ThrottledPacketDataSizeKey returns the key storing the size of the throttled packet data queue for a given chain ID
func ThrottledPacketDataSizeKey(consumerChainID string) []byte {
	return append([]byte{MustGetKeyPrefix("ThrottledPacketDataSizeKey")}, []byte(consumerChainID)...)
}

// ThrottledPacketDataKey returns the key storing the throttled packet data queue for a given chain ID and ibc seq num
func ThrottledPacketDataKey(consumerChainID string, ibcSeqNum uint64) []byte {
	return ChainIdAndUintIdKey(MustGetKeyPrefix("ThrottledPacketDataKey"), consumerChainID, ibcSeqNum)
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
	return ParseChainIdAndUintIdKey(MustGetKeyPrefix("ThrottledPacketDataKey"), key)
}

// GlobalSlashEntryKey returns the key for storing a global slash queue entry.
func GlobalSlashEntryKey(entry GlobalSlashEntry) []byte {
	recvTime := uint64(entry.RecvTime.UTC().UnixNano())
	return ccvtypes.AppendMany(
		// Append byte prefix
		[]byte{MustGetKeyPrefix("GlobalSlashEntryKey")},
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
	expectedPrefix := []byte{MustGetKeyPrefix("GlobalSlashEntryKey")}
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
	return ChainIdAndConsAddrKey(MustGetKeyPrefix("ConsumerValidatorsKey"), chainID, addr.ToSdkConsAddr())

}

// ValidatorsByConsumerAddrKey returns the key under which the mapping from validator addresses
// on consumer chains to validator addresses on the provider chain is stored
func ValidatorsByConsumerAddrKey(chainID string, addr ConsumerConsAddress) []byte {
	return ChainIdAndConsAddrKey(MustGetKeyPrefix("ValidatorsByConsumerAddrKey"), chainID, addr.ToSdkConsAddr())
}

// ConsumerAddrsToPruneKey returns the key under which the
// mapping from VSC ids to consumer validators addresses is stored
func ConsumerAddrsToPruneKey(chainID string, vscID uint64) []byte {
	return ChainIdAndUintIdKey(MustGetKeyPrefix("ConsumerAddrsToPruneKey"), chainID, vscID)
}

// SlashLogKey returns the key to a validator's slash log
func SlashLogKey(providerAddr ProviderConsAddress) []byte {
	return append([]byte{MustGetKeyPrefix("SlashLogKey")}, providerAddr.ToSdkConsAddr().Bytes()...)
}

func VSCMaturedHandledThisBlockKey() []byte {
	return []byte{MustGetKeyPrefix("VSCMaturedHandledThisBlockKey")}
}

// ConsumerRewardDenomsKey returns the key under which consumer reward denoms are stored
func ConsumerRewardDenomsKey(denom string) []byte {
	return append([]byte{MustGetKeyPrefix("ConsumerRewardDenomsKey")}, []byte(denom)...)
}

// EquivocationEvidenceMinHeightKey returns the key storing the minimum height
// of a valid consumer equivocation evidence for a given consumer chain ID
func EquivocationEvidenceMinHeightKey(consumerChainID string) []byte {
	return append([]byte{MustGetKeyPrefix("EquivocationEvidenceMinHeightKey")}, []byte(consumerChainID)...)
}

// ProposedConsumerChainKey returns the key of proposed consumer chainId in consumerAddition gov proposal before voting finishes, the stored key format is prefix|proposalID, value is chainID
func ProposedConsumerChainKey(proposalID uint64) []byte {
	return ccvtypes.AppendMany(
		[]byte{MustGetKeyPrefix("ProposedConsumerChainKey")},
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

// ConsumerValidatorKey returns the key of consumer chain `chainID` and validator with `providerAddr`
func ConsumerValidatorKey(chainID string, providerAddr []byte) []byte {
	prefix := ChainIdWithLenKey(MustGetKeyPrefix("ConsumerValidatorKey"), chainID)
	return append(prefix, providerAddr...)
}

// TopNKey returns the key used to store the Top N value per consumer chain.
// This value corresponds to the N% of the top validators that have to validate the consumer chain.
func TopNKey(chainID string) []byte {
	return ChainIdWithLenKey(MustGetKeyPrefix("TopNKey"), chainID)
}

// ValidatorSetPowerKey returns the key of consumer chain `chainID`
func ValidatorsPowerCapKey(chainID string) []byte {
	return ChainIdWithLenKey(MustGetKeyPrefix("ValidatorsPowerCapKey"), chainID)
}

// ValidatorSetCapKey returns the key of consumer chain `chainID`
func ValidatorSetCapKey(chainID string) []byte {
	return ChainIdWithLenKey(MustGetKeyPrefix("ValidatorSetCapKey"), chainID)
}

// AllowlistCapKey returns the key to a validator's slash log
func AllowlistCapKey(chainID string, providerAddr ProviderConsAddress) []byte {
	return append(ChainIdWithLenKey(MustGetKeyPrefix("AllowlistKey"), chainID), providerAddr.ToSdkConsAddr().Bytes()...)
}

// DenylistCapKey returns the key to a validator's slash log
func DenylistCapKey(chainID string, providerAddr ProviderConsAddress) []byte {
	return append(ChainIdWithLenKey(MustGetKeyPrefix("DenylistKey"), chainID), providerAddr.ToSdkConsAddr().Bytes()...)
}

// OptedInKey returns the key used to store whether a validator is opted in on a consumer chain.
func OptedInKey(chainID string, providerAddr ProviderConsAddress) []byte {
	prefix := ChainIdWithLenKey(MustGetKeyPrefix("OptedInKey"), chainID)
	return append(prefix, providerAddr.ToSdkConsAddr().Bytes()...)
}

// ConsumerRewardsAllocationKey returns the key used to store the ICS rewards per consumer chain
func ConsumerRewardsAllocationKey(chainID string) []byte {
	return append([]byte{MustGetKeyPrefix("ConsumerRewardsAllocationKey")}, []byte(chainID)...)
}

// ConsumerCommissionRateKey returns the key used to store the commission rate per validator per consumer chain.
func ConsumerCommissionRateKey(chainID string, providerAddr ProviderConsAddress) []byte {
	return ChainIdAndConsAddrKey(
		MustGetKeyPrefix("ConsumerCommissionRateKey"),
		chainID,
		providerAddr.ToSdkConsAddr(),
	)
}

func MinimumPowerInTopNKey(chainID string) []byte {
	return ChainIdWithLenKey(MustGetKeyPrefix("MinimumPowerInTopNKey"), chainID)
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

//
// End of generic helpers section
//
