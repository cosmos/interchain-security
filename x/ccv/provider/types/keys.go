package types

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"sort"
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

	// Names for the store keys.
	// Used for storing the byte prefixes in the constant map.
	// See getKeyPrefixes().

	ParametersKeyName = "ParametersKey"

	PortKeyName = "PortKey"

	DeprecatedMaturedUnbondingOpsKeyName = "DeprecatedMaturedUnbondingOpsKey"

	ValidatorSetUpdateIdKeyName = "ValidatorSetUpdateIdKey"

	SlashMeterKeyName = "SlashMeterKey"

	SlashMeterReplenishTimeCandidateKeyName = "SlashMeterReplenishTimeCandidateKey"

	ChainToChannelKeyName = "ChainToChannelKey"

	ChannelToChainKeyName = "ChannelToChainKey"

	ChainToClientKeyName = "ChainToClientKey"

	DeprecatedInitTimeoutTimestampKeyName = "DeprecatedInitTimeoutTimestampKey"

	PendingCAPKeyName = "PendingCAPKey"

	PendingCRPKeyName = "PendingCRPKey"

	DeprecatedUnbondingOpKeyName = "DeprecatedUnbondingOpKey"

	DeprecatedUnbondingOpIndexKeyName = "DeprecatedUnbondingOpIndexKey"

	ValsetUpdateBlockHeightKeyName = "ValsetUpdateBlockHeightKey"

	ConsumerGenesisKeyName = "ConsumerGenesisKey"

	SlashAcksKeyName = "SlashAcksKey"

	InitChainHeightKeyName = "InitChainHeightKey"

	PendingVSCsKeyName = "PendingVSCsKey"

	DeprecatedVscSendTimestampKeyName = "DeprecatedVscSendTimestampKey"

	ThrottledPacketDataSizeKeyName = "ThrottledPacketDataSizeKey"

	ThrottledPacketDataKeyName = "ThrottledPacketDataKey"

	GlobalSlashEntryKeyName = "GlobalSlashEntryKey"

	ConsumerValidatorsKeyName = "ConsumerValidatorsKey"

	ValidatorsByConsumerAddrKeyName = "ValidatorsByConsumerAddrKey"

	DeprecatedKeyAssignmentReplacementsKeyName = "DeprecatedKeyAssignmentReplacementsKey"

	DeprecatedConsumerAddrsToPruneKeyName = "DeprecatedConsumerAddrsToPruneKey"

	SlashLogKeyName = "SlashLogKey"

	ConsumerRewardDenomsKeyName = "ConsumerRewardDenomsKey"

	DeprecatedVSCMaturedHandledThisBlockKeyName = "DeprecatedVSCMaturedHandledThisBlockKey"

	EquivocationEvidenceMinHeightKeyName = "EquivocationEvidenceMinHeightKey"

	ProposedConsumerChainKeyName = "ProposedConsumerChainKey"

	ConsumerValidatorKeyName = "ConsumerValidatorKey"

	OptedInKeyName = "OptedInKey"

	TopNKeyName = "TopNKey"

	ValidatorsPowerCapKeyName = "ValidatorsPowerCapKey"

	ValidatorSetCapKeyName = "ValidatorSetCapKey"

	AllowlistKeyName = "AllowlistKey"

	DenylistKeyName = "DenylistKey"

	ConsumerRewardsAllocationKeyName = "ConsumerRewardsAllocationKey"

	ConsumerCommissionRateKeyName = "ConsumerCommissionRateKey"

	MinimumPowerInTopNKeyName = "MinimumPowerInTopNKey"

	LastProviderConsensusValsKeyName = "LastProviderConsensusValsKey"

	MinStakeKeyName = "MinStakeKey"

	AllowInactiveValidatorsKeyName = "AllowInactiveValidatorsKey"

	ConsumerAddrsToPruneV2KeyName = "ConsumerAddrsToPruneV2Key"
)

// getKeyPrefixes returns a constant map of all the byte prefixes for existing keys
func getKeyPrefixes() map[string]byte {
	return map[string]byte{
		// ParametersKey is the is the key for storing provider's parameters.
		// note that this was set to the max uint8 type value 0xFF in order to protect
		// from using the ICS v5.0.0 provider module by mistake
		ParametersKeyName: byte(0xFF),

		// PortKey defines the key to store the port ID in store
		PortKeyName: 0,

		// MaturedUnbondingOpsKey is the key that stores the list of all unbonding operations ids
		// that have matured from a consumer chain perspective,
		// i.e., no longer waiting on the unbonding period to elapse on any consumer chain
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedMaturedUnbondingOpsKeyName: 1,

		// ValidatorSetUpdateIdKey is the key that stores the current validator set update id
		ValidatorSetUpdateIdKeyName: 2,

		// SlashMeterKey is the key for storing the slash meter
		SlashMeterKeyName: 3,

		// SlashMeterReplenishTimeCandidateKey is the key for storing the slash meter replenish time candidate
		SlashMeterReplenishTimeCandidateKeyName: 4,

		// ChainToChannelKey is the key for storing mapping
		// from chainID to the channel ID that is used to send over validator set changes.
		ChainToChannelKeyName: 5,

		// ChannelToChainKey is the key for storing mapping
		// from the CCV channel ID to the consumer chain ID.
		ChannelToChainKeyName: 6,

		// ChainToClientKey is the key for storing the client ID for a given consumer chainID.
		ChainToClientKeyName: 7,

		// InitTimeoutTimestampKey is the key for storing
		// the init timeout timestamp for a given consumer chainID.
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedInitTimeoutTimestampKeyName: 8,

		// PendingCAPKey is the key for storing pending consumer addition proposals before the spawn time occurs.
		// The key includes the BigEndian timestamp to allow for efficient chronological iteration
		PendingCAPKeyName: 9,

		// PendingCRPKey is the key for storing pending consumer removal proposals before the stop time occurs.
		// The key includes the BigEndian timestamp to allow for efficient chronological iteration
		PendingCRPKeyName: 10,

		// UnbondingOpKey is the key that stores a record of all the ids of consumer chains that
		// need to unbond before a given unbonding operation can unbond on this chain.
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedUnbondingOpKeyName: 11,

		// UnbondingOpIndexKey is key of the index for looking up which unbonding
		// operations are waiting for a given consumer chain to unbond
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedUnbondingOpIndexKeyName: 12,

		// ValsetUpdateBlockHeightKey is the key for storing the mapping from vscIDs to block heights
		ValsetUpdateBlockHeightKeyName: 13,

		// ConsumerGenesisKey stores consumer genesis state material (consensus state and client state) indexed by consumer chain id
		ConsumerGenesisKeyName: 14,

		// SlashAcksKey is the key for storing consensus address of consumer chain validators successfully slashed on the provider chain
		SlashAcksKeyName: 15,

		// InitChainHeightKey is the key for storing the mapping from a chain id to the corresponding block height on the provider
		// this consumer chain was initialized
		InitChainHeightKeyName: 16,

		// PendingVSCsKey is the key for storing pending ValidatorSetChangePacket data
		PendingVSCsKeyName: 17,

		// VscSendTimestampKey is the key for storing
		// the list of VSC sending timestamps for a given consumer chainID.
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedVscSendTimestampKeyName: 18,

		// ThrottledPacketDataSizeKey is the key for storing the size of chain-specific throttled packet data queues
		ThrottledPacketDataSizeKeyName: 19,

		// ThrottledPacketDataKey is the key for storing throttled packet data
		ThrottledPacketDataKeyName: 20,

		// GlobalSlashEntryKey is the key for storing global slash queue entries
		GlobalSlashEntryKeyName: 21,

		// ConsumerValidatorsKey is the key for storing the validator assigned keys for every consumer chain
		ConsumerValidatorsKeyName: 22,

		// ValidatorsByConsumerAddrKey is the key for storing the mapping from validator addresses
		// on consumer chains to validator addresses on the provider chain
		ValidatorsByConsumerAddrKeyName: 23,

		// DeprecatedKeyAssignmentReplacementsKey was the key used to store the key assignments that needed to be replaced in the current block
		// NOTE: This prefix is deprecated, but left in place to avoid consumer state migrations
		// [DEPRECATED]
		DeprecatedKeyAssignmentReplacementsKeyName: 24,

		// ConsumerAddrsToPruneKey is the key for storing the mapping from VSC ids
		// to consumer validators addresses needed for pruning
		// NOTE: This prefix is deprecated, but left in place to avoid consumer state migrations
		// [DEPRECATED]
		DeprecatedConsumerAddrsToPruneKeyName: 25,

		// SlashLogKey is the key for storing the mapping from provider address to boolean
		// denoting whether the provider address has committed any double signign infractions
		SlashLogKeyName: 26,

		// ConsumerRewardDenomsKey is the key for storing a list of consumer reward denoms
		ConsumerRewardDenomsKeyName: 27,

		// VSCMaturedHandledThisBlockKey is the key for storing the number of vsc matured packets
		// handled in the current block
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedVSCMaturedHandledThisBlockKeyName: 28,

		// EquivocationEvidenceMinHeightKey is the key for storing the mapping from consumer chain IDs
		// to the minimum height of a valid consumer equivocation evidence
		EquivocationEvidenceMinHeightKeyName: 29,

		// ProposedConsumerChainKey is the key for storing the consumer chainId in consumerAddition gov proposal submitted before voting finishes
		ProposedConsumerChainKeyName: 30,

		// ConsumerValidatorKey is the key for storing for each consumer chain all the consumer
		// validators in this epoch that are validating the consumer chain
		ConsumerValidatorKeyName: 31,

		// OptedInKey is the key for storing whether a validator is opted in to validate on a consumer chain
		OptedInKeyName: 32,

		// TopNKey is the key for storing the mapping from a consumer chain to the N value of this chain,
		// that corresponds to the N% of the top validators that have to validate this consumer chain
		TopNKeyName: 33,

		// ValidatorsPowerCapKey is the key for  storing the mapping from a consumer chain to the power-cap value of this chain,
		// that corresponds to p% such that no validator can have more than p% of the voting power on the consumer chain.
		// Operates on a best-effort basis.
		ValidatorsPowerCapKeyName: 34,

		// ValidatorSetCapKey is the key for storing the mapping from a consumer chain to the validator-set cap value
		// of this chain.
		ValidatorSetCapKeyName: 35,

		// AllowlistKey is the key for storing the mapping from a consumer chain to the set of validators that are
		// allowlisted.
		AllowlistKeyName: 36,

		// DenylistKey is the key for storing the mapping from a consumer chain to the set of validators that are
		// denylisted.
		DenylistKeyName: 37,

		// ConsumerRewardsAllocationKey is the key for storing for each consumer the ICS rewards
		// allocated to the consumer rewards pool
		ConsumerRewardsAllocationKeyName: 38,

		// ConsumerCommissionRateKey is the key for storing the commission rate
		// per validator per consumer chain
		ConsumerCommissionRateKeyName: 39,

		// MinimumPowerInTopNKey is the key for storing the
		// minimum power required to be in the top N per consumer chain.
		MinimumPowerInTopNKeyName: 40,

		// ConsumerAddrsToPruneV2Key is the key for storing
		// consumer validators addresses that need to be pruned.
		ConsumerAddrsToPruneV2KeyName: 41,

		// LastProviderConsensusValsKey is the byte prefix for storing the last validator set
		// sent to the consensus engine of the provider chain
		LastProviderConsensusValsKeyName: 42,

		// MinStakeKey is the byte prefix for storing the mapping from consumer chains to the minimum stake required to be a validator on the consumer chain
		// The minimum stake must be stored on the provider chain, not on the consumer chain itself, since it filters out
		// validators from the VSCPackets that we send to the consumer chain.
		MinStakeKeyName: 43,

		// AllowInactiveValidatorsKey is the byte prefix for storing the mapping from consumer chains to the boolean value
		// that determines whether inactive validators can validate on that chain
		AllowInactiveValidatorsKeyName: 44,

		// NOTE: DO NOT ADD NEW BYTE PREFIXES HERE WITHOUT ADDING THEM TO TestPreserveBytePrefix() IN keys_test.go
	}
}

// mustGetKeyPrefix returns the key prefix for a given key.
// It panics if there is not byte prefix for the index.
func mustGetKeyPrefix(key string) byte {
	keyPrefixes := getKeyPrefixes()
	if prefix, found := keyPrefixes[key]; !found {
		panic(fmt.Sprintf("could not find key prefix for index %s", key))
	} else {
		return prefix
	}
}

// GetAllKeyPrefixes returns all the key prefixes.
// Only used for testing
func GetAllKeyPrefixes() []byte {
	prefixMap := getKeyPrefixes()
	keys := make([]string, 0, len(prefixMap))
	for k := range prefixMap {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	prefixList := make([]byte, 0, len(prefixMap))
	for _, k := range keys {
		prefixList = append(prefixList, prefixMap[k])
	}
	return prefixList
}

// GetAllKeys returns the names of all the keys.
// Only used for testing
func GetAllKeyNames() []string {
	prefixMap := getKeyPrefixes()
	keys := make([]string, 0, len(prefixMap))
	for k := range prefixMap {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

//
// Fully defined key func section
//

// ParametersKey returns the key for the parameters of the provider module in the store
func ParametersKey() []byte {
	return []byte{mustGetKeyPrefix(ParametersKeyName)}
}

// PortKey returns the key to the port ID in the store
func PortKey() []byte {
	return []byte{mustGetKeyPrefix(PortKeyName)}
}

// ValidatorSetUpdateIdKey is the key that stores the current validator set update id
func ValidatorSetUpdateIdKey() []byte {
	return []byte{mustGetKeyPrefix(ValidatorSetUpdateIdKeyName)}
}

// SlashMeterKey returns the key storing the slash meter
func SlashMeterKey() []byte {
	return []byte{mustGetKeyPrefix(SlashMeterKeyName)}
}

// SlashMeterReplenishTimeCandidateKey returns the key storing the slash meter replenish time candidate
func SlashMeterReplenishTimeCandidateKey() []byte {
	return []byte{mustGetKeyPrefix(SlashMeterReplenishTimeCandidateKeyName)}
}

// ChainToChannelKey returns the key under which the CCV channel ID will be stored for the given consumer chain.
func ChainToChannelKey(chainID string) []byte {
	return append([]byte{mustGetKeyPrefix(ChainToChannelKeyName)}, []byte(chainID)...)
}

// ChannelToChainKeyPrefix returns the key prefix for storing the consumer chain IDs.
func ChannelToChainKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(ChannelToChainKeyName)}
}

// ChannelToChainKey returns the key under which the consumer chain ID will be stored for the given channelID.
func ChannelToChainKey(channelID string) []byte {
	return append(ChannelToChainKeyPrefix(), []byte(channelID)...)
}

// ChainToClientKeyPrefix returns the key prefix for storing the clientID for the given chainID.
func ChainToClientKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(ChainToClientKeyName)}
}

// ChainToClientKey returns the key under which the clientID for the given chainID is stored.
func ChainToClientKey(chainID string) []byte {
	return append(ChainToClientKeyPrefix(), []byte(chainID)...)
}

// PendingCAPKeyPrefix returns the key prefix for storing a pending consumer addition proposal
func PendingCAPKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(PendingCAPKeyName)}
}

// PendingCAPKey returns the key under which a pending consumer addition proposal is stored.
// The key has the following format: PendingCAPKeyPrefix | timestamp.UnixNano() | chainID
func PendingCAPKey(timestamp time.Time, chainID string) []byte {
	ts := uint64(timestamp.UTC().UnixNano())
	return ccvtypes.AppendMany(
		// Append the prefix
		PendingCAPKeyPrefix(),
		// Append the time
		sdk.Uint64ToBigEndian(ts),
		// Append the chainId
		[]byte(chainID),
	)
}

// PendingCRPKeyPrefix returns the key prefix for storing pending consumer removal proposals.
func PendingCRPKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(PendingCRPKeyName)}
}

// PendingCRPKey returns the key under which pending consumer removal proposals are stored.
// The key has the following format: PendingCRPKeyPrefix | timestamp.UnixNano() | chainID
func PendingCRPKey(timestamp time.Time, chainID string) []byte {
	ts := uint64(timestamp.UTC().UnixNano())
	return ccvtypes.AppendMany(
		// Append the prefix
		PendingCRPKeyPrefix(),
		// Append the time
		sdk.Uint64ToBigEndian(ts),
		// Append the chainId
		[]byte(chainID),
	)
}

// ValsetUpdateBlockHeightKeyPrefix returns the key prefix that storing the mapping from valset update ID to block height
func ValsetUpdateBlockHeightKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(ValsetUpdateBlockHeightKeyName)}
}

// ValsetUpdateBlockHeightKey returns the key that storing the mapping from valset update ID to block height
func ValsetUpdateBlockHeightKey(valsetUpdateId uint64) []byte {
	vuidBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(vuidBytes, valsetUpdateId)
	return append(ValsetUpdateBlockHeightKeyPrefix(), vuidBytes...)
}

// ConsumerGenesisKey returns the key corresponding to consumer genesis state material
// (consensus state and client state) indexed by consumer chain id
func ConsumerGenesisKey(chainID string) []byte {
	return append([]byte{mustGetKeyPrefix(ConsumerGenesisKeyName)}, []byte(chainID)...)
}

// SlashAcksKey returns the key under which slashing acks are stored for a given chain ID
func SlashAcksKey(chainID string) []byte {
	return append([]byte{mustGetKeyPrefix(SlashAcksKeyName)}, []byte(chainID)...)
}

// InitChainHeightKey returns the key under which the block height for a given chain ID is stored
func InitChainHeightKey(chainID string) []byte {
	return append([]byte{mustGetKeyPrefix(InitChainHeightKeyName)}, []byte(chainID)...)
}

// PendingVSCsKey returns the key under which
// pending ValidatorSetChangePacket data is stored for a given chain ID
func PendingVSCsKey(chainID string) []byte {
	return append([]byte{mustGetKeyPrefix(PendingVSCsKeyName)}, []byte(chainID)...)
}

// ThrottledPacketDataSizeKey returns the key storing the size of the throttled packet data queue for a given chain ID
func ThrottledPacketDataSizeKey(consumerChainID string) []byte {
	return append([]byte{mustGetKeyPrefix(ThrottledPacketDataSizeKeyName)}, []byte(consumerChainID)...)
}

// ThrottledPacketDataKeyPrefix returns the key prefix for storing the throttled packet data queue
func ThrottledPacketDataKeyPrefix() byte {
	return mustGetKeyPrefix(ThrottledPacketDataKeyName)
}

// ThrottledPacketDataKey returns the key for storing the throttled packet data queue for a given chain ID and ibc seq num
func ThrottledPacketDataKey(consumerChainID string, ibcSeqNum uint64) []byte {
	return ChainIdAndUintIdKey(ThrottledPacketDataKeyPrefix(), consumerChainID, ibcSeqNum)
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
	return ParseChainIdAndUintIdKey(ThrottledPacketDataKeyPrefix(), key)
}

// ConsumerValidatorsKey returns the key for storing the validator assigned keys for every consumer chain
func ConsumerValidatorsKeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerValidatorsKeyName)
}

// ConsumerValidatorsKey returns the key under which the
// validator assigned keys for every consumer chain are stored
func ConsumerValidatorsKey(chainID string, addr ProviderConsAddress) []byte {
	return ChainIdAndConsAddrKey(ConsumerValidatorsKeyPrefix(), chainID, addr.ToSdkConsAddr())
}

// ValidatorsByConsumerAddrKeyPrefix returns the key prefix for storing the mapping from validator addresses
// on consumer chains to validator addresses on the provider chain
func ValidatorsByConsumerAddrKeyPrefix() byte {
	return mustGetKeyPrefix(ValidatorsByConsumerAddrKeyName)
}

// ValidatorsByConsumerAddrKey returns the key for storing the mapping from validator addresses
// on consumer chains to validator addresses on the provider chain
func ValidatorsByConsumerAddrKey(chainID string, addr ConsumerConsAddress) []byte {
	return ChainIdAndConsAddrKey(ValidatorsByConsumerAddrKeyPrefix(), chainID, addr.ToSdkConsAddr())
}

// SlashLogKey returns the key to a validator's slash log
func SlashLogKey(providerAddr ProviderConsAddress) []byte {
	return append([]byte{mustGetKeyPrefix(SlashLogKeyName)}, providerAddr.ToSdkConsAddr().Bytes()...)
}

// ConsumerRewardDenomsKeyPrefix returns the key prefix for storing consumer reward denoms
func ConsumerRewardDenomsKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(ConsumerRewardDenomsKeyName)}
}

// ConsumerRewardDenomsKey returns the key for storing consumer reward denoms
func ConsumerRewardDenomsKey(denom string) []byte {
	return append(ConsumerRewardDenomsKeyPrefix(), []byte(denom)...)
}

// EquivocationEvidenceMinHeightKey returns the key storing the minimum height
// of a valid consumer equivocation evidence for a given consumer chain ID
func EquivocationEvidenceMinHeightKey(consumerChainID string) []byte {
	return append([]byte{mustGetKeyPrefix(EquivocationEvidenceMinHeightKeyName)}, []byte(consumerChainID)...)
}

// ProposedConsumerChainKeyPrefix returns the key prefix for storing proposed consumer chainId
// in consumerAddition gov proposal before voting finishes
func ProposedConsumerChainKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(ProposedConsumerChainKeyName)}
}

// ProposedConsumerChainKey returns the key of proposed consumer chainId in consumerAddition gov proposal before voting finishes, the stored key format is prefix|proposalID, value is chainID
func ProposedConsumerChainKey(proposalID uint64) []byte {
	return ccvtypes.AppendMany(
		ProposedConsumerChainKeyPrefix(),
		sdk.Uint64ToBigEndian(proposalID),
	)
}

// ParseProposedConsumerChainKey get the proposalID in the key
func ParseProposedConsumerChainKey(bz []byte) (uint64, error) {
	expectedPrefix := ProposedConsumerChainKeyPrefix()
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return 0, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	proposalID := sdk.BigEndianToUint64(bz[prefixL:])

	return proposalID, nil
}

// ConsumerValidatorKeyPrefix returns the key prefix for storing consumer validators
func ConsumerValidatorKeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerValidatorKeyName)
}

// ConsumerValidatorKey returns the key for storing consumer validators
// for the given consumer chain `chainID` and validator with `providerAddr`
func ConsumerValidatorKey(chainID string, providerAddr []byte) []byte {
	prefix := ChainIdWithLenKey(ConsumerValidatorKeyPrefix(), chainID)
	return append(prefix, providerAddr...)
}

// TopNKey returns the key used to store the Top N value per consumer chain.
// This value corresponds to the N% of the top validators that have to validate the consumer chain.
func TopNKey(chainID string) []byte {
	return ChainIdWithLenKey(mustGetKeyPrefix(TopNKeyName), chainID)
}

// ValidatorSetPowerKey returns the key of consumer chain `chainID`
func ValidatorsPowerCapKey(chainID string) []byte {
	return ChainIdWithLenKey(mustGetKeyPrefix(ValidatorsPowerCapKeyName), chainID)
}

// ValidatorSetCapKey returns the key of consumer chain `chainID`
func ValidatorSetCapKey(chainID string) []byte {
	return ChainIdWithLenKey(mustGetKeyPrefix(ValidatorSetCapKeyName), chainID)
}

// AllowlistKeyPrefix returns the key prefix for storing consumer chains allowlists
func AllowlistKeyPrefix() byte {
	return mustGetKeyPrefix(AllowlistKeyName)
}

// AllowlistKey returns the key for storing consumer chains allowlists
func AllowlistKey(chainID string, providerAddr ProviderConsAddress) []byte {
	return append(
		ChainIdWithLenKey(AllowlistKeyPrefix(), chainID),
		providerAddr.ToSdkConsAddr().Bytes()...,
	)
}

// DenylistKeyPrefix returns the key prefix for storing consumer chains denylists
func DenylistKeyPrefix() byte {
	return mustGetKeyPrefix(DenylistKeyName)
}

// DenylistKey returns the key for storing consumer chains denylists
func DenylistKey(chainID string, providerAddr ProviderConsAddress) []byte {
	return append(
		ChainIdWithLenKey(DenylistKeyPrefix(), chainID),
		providerAddr.ToSdkConsAddr().Bytes()...,
	)
}

// OptedInKeyPrefix returns the key prefix for storing whether a validator is opted in on a consumer chain.
func OptedInKeyPrefix() byte {
	return mustGetKeyPrefix(OptedInKeyName)
}

// OptedInKey returns the key used to store whether a validator is opted in on a consumer chain.
func OptedInKey(chainID string, providerAddr ProviderConsAddress) []byte {
	prefix := ChainIdWithLenKey(OptedInKeyPrefix(), chainID)
	return append(prefix, providerAddr.ToSdkConsAddr().Bytes()...)
}

// ConsumerRewardsAllocationKey returns the key used to store the ICS rewards per consumer chain
func ConsumerRewardsAllocationKey(chainID string) []byte {
	return append([]byte{mustGetKeyPrefix(ConsumerRewardsAllocationKeyName)}, []byte(chainID)...)
}

// ConsumerCommissionRateKeyPrefix returns the key prefix for storing the commission rate per validator per consumer chain.
func ConsumerCommissionRateKeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerCommissionRateKeyName)
}

// ConsumerCommissionRateKey returns the key used to store the commission rate per validator per consumer chain.
func ConsumerCommissionRateKey(chainID string, providerAddr ProviderConsAddress) []byte {
	return ChainIdAndConsAddrKey(
		ConsumerCommissionRateKeyPrefix(),
		chainID,
		providerAddr.ToSdkConsAddr(),
	)
}

func MinimumPowerInTopNKey(chainID string) []byte {
	return ChainIdWithLenKey(mustGetKeyPrefix(MinimumPowerInTopNKeyName), chainID)
}

// ConsumerAddrsToPruneV2KeyPrefix returns the key prefix for storing the consumer validators
// addresses that need to be pruned. These are stored as a
// (chainID, ts) -> (consumer_address1, consumer_address2, ...) mapping, where ts is the
// timestamp at which the consumer validators addresses can be pruned.
func ConsumerAddrsToPruneV2KeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerAddrsToPruneV2KeyName)
}

// ConsumerAddrsToPruneV2Key returns the key for storing the consumer validators
// addresses that need to be pruned.
func ConsumerAddrsToPruneV2Key(chainID string, pruneTs time.Time) []byte {
	return ChainIdAndTsKey(ConsumerAddrsToPruneV2KeyPrefix(), chainID, pruneTs)
}

// LastProviderConsensusValsPrefix returns the key prefix for storing the last validator set sent to the consensus engine of the provider chain
func LastProviderConsensusValsPrefix() []byte {
	return []byte{mustGetKeyPrefix(LastProviderConsensusValsKeyName)}
}

// MinStakeKey returns the key used to store the minimum stake required to validate on consumer chain `chainID`
func MinStakeKey(chainID string) []byte {
	return ChainIdWithLenKey(mustGetKeyPrefix(MinStakeKeyName), chainID)
}

func AllowInactiveValidatorsKey(chainID string) []byte {
	return ChainIdWithLenKey(mustGetKeyPrefix(AllowInactiveValidatorsKeyName), chainID)
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
