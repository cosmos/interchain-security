package types

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"sort"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
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

	ConsumerIdToChannelIdKeyName = "ConsumerIdToChannelIdKey"

	ChannelIdToConsumerIdKeyName = "ChannelToConsumerIdKey"

	ConsumerIdToClientIdKeyName = "ConsumerIdToClientIdKey"

	DeprecatedInitTimeoutTimestampKeyName = "DeprecatedInitTimeoutTimestampKey"

	DeprecatedPendingCAPKeyName = "DeprecatedPendingCAPKey"

	DeprecatedPendingCRPKeyName = "DeprecatedPendingCRPKey"

	DeprecatedUnbondingOpKeyName = "DeprecatedUnbondingOpKey"

	DeprecatedUnbondingOpIndexKeyName = "DeprecatedUnbondingOpIndexKey"

	ValsetUpdateBlockHeightKeyName = "ValsetUpdateBlockHeightKey"

	ConsumerGenesisKeyName = "ConsumerGenesisKey"

	SlashAcksKeyName = "SlashAcksKey"

	InitChainHeightKeyName = "InitChainHeightKey"

	PendingVSCsKeyName = "PendingVSCsKey"

	DeprecatedVscSendTimestampKeyName = "DeprecatedVscSendTimestampKey"

	DeprecatedThrottledPacketDataSizeKeyName = "DeprecatedThrottledPacketDataSizeKey"

	DeprecatedThrottledPacketDataKeyName = "DeprecatedThrottledPacketDataKey"

	DeprecatedGlobalSlashEntryKeyName = "DeprecatedGlobalSlashEntryKey"

	ConsumerValidatorsKeyName = "ConsumerValidatorsKey"

	ValidatorsByConsumerAddrKeyName = "ValidatorsByConsumerAddrKey"

	DeprecatedKeyAssignmentReplacementsKeyName = "DeprecatedKeyAssignmentReplacementsKey"

	DeprecatedConsumerAddrsToPruneKeyName = "DeprecatedConsumerAddrsToPruneKey"

	SlashLogKeyName = "SlashLogKey"

	ConsumerRewardDenomsKeyName = "ConsumerRewardDenomsKey"

	DeprecatedVSCMaturedHandledThisBlockKeyName = "DeprecatedVSCMaturedHandledThisBlockKey"

	EquivocationEvidenceMinHeightKeyName = "EquivocationEvidenceMinHeightKey"

	DeprecatedProposedConsumerChainKeyName = "DeprecatedProposedConsumerChainKey"

	ConsumerValidatorKeyName = "ConsumerValidatorKey"

	OptedInKeyName = "OptedInKey"

	DeprecatedTopNKeyName = "DeprecatedTopNKey"

	DeprecatedValidatorsPowerCapKeyName = "DeprecatedValidatorsPowerCapKey"

	DeprecatedValidatorSetCapKeyName = "DeprecatedValidatorSetCapKey"

	AllowlistKeyName = "AllowlistKey"

	DenylistKeyName = "DenylistKey"

	ConsumerRewardsAllocationKeyName = "ConsumerRewardsAllocationKey"

	ConsumerCommissionRateKeyName = "ConsumerCommissionRateKey"

	MinimumPowerInTopNKeyName = "MinimumPowerInTopNKey"

	LastProviderConsensusValsKeyName = "LastProviderConsensusValsKey"

	ConsumerAddrsToPruneV2KeyName = "ConsumerAddrsToPruneV2Key"

	ConsumerIdKeyName = "ConsumerIdKey"

	ConsumerIdToChainIdKeyName = "ConsumerIdToChainIdKey"

	ConsumerIdToOwnerAddressKeyName = "ConsumerIdToOwnerAddress"

	ConsumerIdToConsumerMetadataKeyName = "ConsumerIdToMetadataKey"

	ConsumerIdToInitializationParametersKeyName = "ConsumerIdToInitializationParametersKey"

	ConsumerIdToPowerShapingParameters = "ConsumerIdToPowerShapingParametersKey"

	ConsumerIdToPhaseKeyName = "ConsumerIdToPhaseKey"

	ConsumerIdToRemovalTimeKeyName = "ConsumerIdToRemovalTimeKey"

	SpawnTimeToConsumerIdsKeyName = "SpawnTimeToConsumerIdsKeyName"

	RemovalTimeToConsumerIdsKeyName = "RemovalTimeToConsumerIdsKeyName"

	ProviderConsAddrToOptedInConsumerIdsKeyName = "ProviderConsAddrToOptedInConsumerIdsKeyName"

	ClientIdToConsumerIdKeyName = "ClientIdToConsumerIdKey"
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

		// ConsumerIdToChannelIdKey is the key for storing mapping
		// from chainID to the channel ID that is used to send over validator set changes.
		ConsumerIdToChannelIdKeyName: 5,

		// ChannelToConsumerIdKey is the key for storing mapping
		// from the CCV channel ID to the consumer chain ID.
		ChannelIdToConsumerIdKeyName: 6,

		// ConsumerIdToClientIdKey is the key for storing the client ID for a given consumer chainID.
		ConsumerIdToClientIdKeyName: 7,

		// InitTimeoutTimestampKey is the key for storing
		// the init timeout timestamp for a given consumer chainID.
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedInitTimeoutTimestampKeyName: 8,

		// PendingCAPKey is the key for storing pending consumer addition proposals before the spawn time occurs.
		// The key includes the BigEndian timestamp to allow for efficient chronological iteration
		// [DEPRECATED]
		DeprecatedPendingCAPKeyName: 9,

		// PendingCRPKey is the key for storing pending consumer removal proposals before the stop time occurs.
		// The key includes the BigEndian timestamp to allow for efficient chronological iteration
		// [DEPRECATED]
		DeprecatedPendingCRPKeyName: 10,

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
		// [DEPRECATED]
		DeprecatedThrottledPacketDataSizeKeyName: 19,

		// ThrottledPacketDataKey is the key for storing throttled packet data
		// [DEPRECATED]
		DeprecatedThrottledPacketDataKeyName: 20,

		// GlobalSlashEntryKey is the key for storing global slash queue entries
		// [DEPRECATED]
		DeprecatedGlobalSlashEntryKeyName: 21,

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
		// [DEPRECATED]
		DeprecatedProposedConsumerChainKeyName: 30,

		// ConsumerValidatorKey is the key for storing for each consumer chain all the consumer
		// validators in this epoch that are validating the consumer chain
		ConsumerValidatorKeyName: 31,

		// OptedInKey is the key for storing whether a validator is opted in to validate on a consumer chain
		OptedInKeyName: 32,

		// DeprecatedTopNKey is the key for storing the mapping from a consumer chain to the N value of this chain,
		// that corresponds to the N% of the top validators that have to validate this consumer chain
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedTopNKeyName: 33,

		// DeprecatedValidatorsPowerCapKey is the key for  storing the mapping from a consumer chain to the power-cap value of this chain,
		// that corresponds to p% such that no validator can have more than p% of the voting power on the consumer chain.
		// Operates on a best-effort basis.
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedValidatorsPowerCapKeyName: 34,

		// DeprecatedValidatorSetCapKey is the key for storing the mapping from a consumer chain to the validator-set cap value
		// of this chain.
		// NOTE: This prefix is deprecated, but left in place to avoid state migrations
		// [DEPRECATED]
		DeprecatedValidatorSetCapKeyName: 35,

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

		// ConsumerIdKeyName is the key for storing the consumer id for the next registered consumer chain
		ConsumerIdKeyName: 43,

		// ConsumerIdToChainIdKeyName is the key for storing the chain id for the given consumer id
		ConsumerIdToChainIdKeyName: 44,

		// ConsumerIdToOwnerAddressKeyName is the key for storing the owner address for the given consumer id
		ConsumerIdToOwnerAddressKeyName: 45,

		// ConsumerIdToConsumerMetadataKeyName is the key for storing the metadata for the given consumer id
		ConsumerIdToConsumerMetadataKeyName: 46,

		// ConsumerIdToInitializationParametersKeyName is the key for storing the initialization parameters for the given consumer id
		ConsumerIdToInitializationParametersKeyName: 47,

		// ConsumerIdToPowerShapingParameters is the key for storing the power-shaping parameters for the given consumer id
		ConsumerIdToPowerShapingParameters: 48,

		// ConsumerIdToPhaseKeyName is the key for storing the phase of a consumer chain with the given consumer id
		ConsumerIdToPhaseKeyName: 49,

		// ConsumerIdToRemovalTimeKeyName is the key for storing the removal time of a consumer chain that is to be removed
		ConsumerIdToRemovalTimeKeyName: 50,

		// SpawnTimeToConsumerIdKeyName is the key for storing pending initialized consumers that are to be launched.
		// For a specific spawn time, it might store multiple consumer chain ids for chains that are to be launched.
		SpawnTimeToConsumerIdsKeyName: 51,

		// RemovalTimeToConsumerIdsKeyName is the key for storing pending launched consumers that are to be removed.
		// For a specific removal time, it might store multiple consumer chain ids for chains that are to be removed.
		RemovalTimeToConsumerIdsKeyName: 52,

		// ProviderConsAddrToOptedInConsumerIdsKeyName is the key for storing all the consumer ids that a validator
		// is currently opted in to.
		ProviderConsAddrToOptedInConsumerIdsKeyName: 53,

		// ClientIdToConsumerIdKeyName is the key for storing the consumer id for the given client id
		ClientIdToConsumerIdKeyName: 54,

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

// ConsumerIdToChannelIdKey returns the key under which the CCV channel ID will be stored for the given consumer chain.
func ConsumerIdToChannelIdKey(consumerId string) []byte {
	return append([]byte{mustGetKeyPrefix(ConsumerIdToChannelIdKeyName)}, []byte(consumerId)...)
}

// ChannelIdToConsumerIdKeyPrefix returns the key prefix for storing the consumer chain ids.
func ChannelIdToConsumerIdKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(ChannelIdToConsumerIdKeyName)}
}

// ChannelToConsumerIdKey returns the key under which the consumer chain id will be stored for the given channelId.
func ChannelToConsumerIdKey(channelId string) []byte {
	return append(ChannelIdToConsumerIdKeyPrefix(), []byte(channelId)...)
}

// ConsumerIdToClientIdKeyPrefix returns the key prefix for storing the clientId for the given consumerId.
func ConsumerIdToClientIdKeyPrefix() []byte {
	return []byte{mustGetKeyPrefix(ConsumerIdToClientIdKeyName)}
}

// ConsumerIdToClientIdKey returns the key under which the clientId for the given consumerId is stored.
func ConsumerIdToClientIdKey(consumerId string) []byte {
	return append(ConsumerIdToClientIdKeyPrefix(), []byte(consumerId)...)
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
// (consensus state and client state) indexed by consumer id
func ConsumerGenesisKey(consumerId string) []byte {
	return append([]byte{mustGetKeyPrefix(ConsumerGenesisKeyName)}, []byte(consumerId)...)
}

// SlashAcksKey returns the key under which slashing acks are stored for a given consumer id
func SlashAcksKey(consumerId string) []byte {
	return append([]byte{mustGetKeyPrefix(SlashAcksKeyName)}, []byte(consumerId)...)
}

// InitChainHeightKey returns the key under which the block height for a given consumer id is stored
func InitChainHeightKey(consumerId string) []byte {
	return append([]byte{mustGetKeyPrefix(InitChainHeightKeyName)}, []byte(consumerId)...)
}

// PendingVSCsKey returns the key under which
// pending ValidatorSetChangePacket data is stored for a given consumer id
func PendingVSCsKey(consumerId string) []byte {
	return append([]byte{mustGetKeyPrefix(PendingVSCsKeyName)}, []byte(consumerId)...)
}

// ConsumerValidatorsKey returns the key for storing the validator assigned keys for every consumer chain
func ConsumerValidatorsKeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerValidatorsKeyName)
}

// ConsumerValidatorsKey returns the key under which the
// validator assigned keys for every consumer chain are stored
func ConsumerValidatorsKey(consumerId string, addr ProviderConsAddress) []byte {
	return StringIdAndConsAddrKey(ConsumerValidatorsKeyPrefix(), consumerId, addr.ToSdkConsAddr())
}

// ValidatorsByConsumerAddrKeyPrefix returns the key prefix for storing the mapping from validator addresses
// on consumer chains to validator addresses on the provider chain
func ValidatorsByConsumerAddrKeyPrefix() byte {
	return mustGetKeyPrefix(ValidatorsByConsumerAddrKeyName)
}

// ValidatorsByConsumerAddrKey returns the key for storing the mapping from validator addresses
// on consumer chains to validator addresses on the provider chain
func ValidatorsByConsumerAddrKey(consumerId string, addr ConsumerConsAddress) []byte {
	return StringIdAndConsAddrKey(ValidatorsByConsumerAddrKeyPrefix(), consumerId, addr.ToSdkConsAddr())
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
// of a valid consumer equivocation evidence for a given consumer id
func EquivocationEvidenceMinHeightKey(consumerId string) []byte {
	return append([]byte{mustGetKeyPrefix(EquivocationEvidenceMinHeightKeyName)}, []byte(consumerId)...)
}

// ConsumerValidatorKeyPrefix returns the key prefix for storing consumer validators
func ConsumerValidatorKeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerValidatorKeyName)
}

// ConsumerValidatorKey returns the key for storing consumer validators
// for the given consumer chain `consumerId` and validator with `providerAddr`
func ConsumerValidatorKey(consumerId string, providerAddr []byte) []byte {
	return StringIdAndConsAddrKey(ConsumerValidatorKeyPrefix(), consumerId, sdk.ConsAddress(providerAddr))
}

// AllowlistKeyPrefix returns the key prefix for storing consumer chains allowlists
func AllowlistKeyPrefix() byte {
	return mustGetKeyPrefix(AllowlistKeyName)
}

// AllowlistKey returns the key for storing consumer chains allowlists
func AllowlistKey(consumerId string, providerAddr ProviderConsAddress) []byte {
	return StringIdAndConsAddrKey(AllowlistKeyPrefix(), consumerId, providerAddr.ToSdkConsAddr())
}

// DenylistKeyPrefix returns the key prefix for storing consumer chains denylists
func DenylistKeyPrefix() byte {
	return mustGetKeyPrefix(DenylistKeyName)
}

// DenylistKey returns the key for storing consumer chains denylists
func DenylistKey(consumerId string, providerAddr ProviderConsAddress) []byte {
	return StringIdAndConsAddrKey(DenylistKeyPrefix(), consumerId, providerAddr.ToSdkConsAddr())
}

// OptedInKeyPrefix returns the key prefix for storing whether a validator is opted in on a consumer chain.
func OptedInKeyPrefix() byte {
	return mustGetKeyPrefix(OptedInKeyName)
}

// OptedInKey returns the key used to store whether a validator is opted in on a consumer chain.
func OptedInKey(consumerId string, providerAddr ProviderConsAddress) []byte {
	return StringIdAndConsAddrKey(OptedInKeyPrefix(), consumerId, providerAddr.ToSdkConsAddr())
}

// ConsumerRewardsAllocationKey returns the key used to store the ICS rewards per consumer chain
func ConsumerRewardsAllocationKey(consumerId string) []byte {
	return append([]byte{mustGetKeyPrefix(ConsumerRewardsAllocationKeyName)}, []byte(consumerId)...)
}

// ConsumerCommissionRateKeyPrefix returns the key prefix for storing the commission rate per validator per consumer chain.
func ConsumerCommissionRateKeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerCommissionRateKeyName)
}

// ConsumerCommissionRateKey returns the key used to store the commission rate per validator per consumer chain.
func ConsumerCommissionRateKey(consumerId string, providerAddr ProviderConsAddress) []byte {
	return StringIdAndConsAddrKey(
		ConsumerCommissionRateKeyPrefix(),
		consumerId,
		providerAddr.ToSdkConsAddr(),
	)
}

func MinimumPowerInTopNKey(consumerId string) []byte {
	return StringIdWithLenKey(mustGetKeyPrefix(MinimumPowerInTopNKeyName), consumerId)
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
func ConsumerAddrsToPruneV2Key(consumerId string, pruneTs time.Time) []byte {
	return StringIdAndTsKey(ConsumerAddrsToPruneV2KeyPrefix(), consumerId, pruneTs)
}

// LastProviderConsensusValsPrefix returns the key prefix for storing the last validator set sent to the consensus engine of the provider chain
func LastProviderConsensusValsPrefix() []byte {
	return []byte{mustGetKeyPrefix(LastProviderConsensusValsKeyName)}
}

// ConsumerIdKey returns the key used to store the consumerId of the next registered chain
func ConsumerIdKey() []byte {
	return []byte{mustGetKeyPrefix(ConsumerIdKeyName)}
}

// ConsumerIdToChainIdKey returns the key used to store the chain id of this consumer id
func ConsumerIdToChainIdKey(consumerId string) []byte {
	return StringIdWithLenKey(mustGetKeyPrefix(ConsumerIdToChainIdKeyName), consumerId)
}

// ConsumerIdToOwnerAddressKey returns the owner address of this consumer id
func ConsumerIdToOwnerAddressKey(consumerId string) []byte {
	return StringIdWithLenKey(mustGetKeyPrefix(ConsumerIdToOwnerAddressKeyName), consumerId)
}

// ConsumerIdToMetadataKeyPrefix returns the key prefix for storing consumer metadata
func ConsumerIdToMetadataKeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerIdToConsumerMetadataKeyName)
}

// ConsumerIdToMetadataKey returns the key used to store the metadata that corresponds to this consumer id
func ConsumerIdToMetadataKey(consumerId string) []byte {
	return StringIdWithLenKey(ConsumerIdToMetadataKeyPrefix(), consumerId)
}

// ConsumerIdToInitializationParametersKeyPrefix returns the key prefix for storing consumer initialization parameters
func ConsumerIdToInitializationParametersKeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerIdToInitializationParametersKeyName)
}

// ConsumerIdToInitializationParametersKey returns the key used to store the initialization parameters that corresponds to this consumer id
func ConsumerIdToInitializationParametersKey(consumerId string) []byte {
	return StringIdWithLenKey(ConsumerIdToInitializationParametersKeyPrefix(), consumerId)
}

// ConsumerIdToPowerShapingParametersKey returns the key used to store the power-shaping parameters that corresponds to this consumer id
func ConsumerIdToPowerShapingParametersKey(consumerId string) []byte {
	return StringIdWithLenKey(mustGetKeyPrefix(ConsumerIdToPowerShapingParameters), consumerId)
}

// ConsumerIdToPhaseKey returns the key used to store the phase that corresponds to this consumer id
func ConsumerIdToPhaseKey(consumerId string) []byte {
	return StringIdWithLenKey(mustGetKeyPrefix(ConsumerIdToPhaseKeyName), consumerId)
}

// ConsumerIdToRemovalTimeKeyPrefix returns the key prefix for storing the removal times of consumer chains
// that are about to be removed
func ConsumerIdToRemovalTimeKeyPrefix() byte {
	return mustGetKeyPrefix(ConsumerIdToRemovalTimeKeyName)
}

// ConsumerIdToRemovalTimeKey returns the key used to store the removal time that corresponds to a to-be-removed chain with consumer id
func ConsumerIdToRemovalTimeKey(consumerId string) []byte {
	return StringIdWithLenKey(ConsumerIdToRemovalTimeKeyPrefix(), consumerId)
}

// SpawnTimeToConsumerIdsKeyPrefix returns the key prefix for storing pending chains that are to be launched
func SpawnTimeToConsumerIdsKeyPrefix() byte {
	return mustGetKeyPrefix(SpawnTimeToConsumerIdsKeyName)
}

// SpawnTimeToConsumerIdsKey returns the key prefix for storing the spawn times of consumer chains
// that are about to be launched
func SpawnTimeToConsumerIdsKey(spawnTime time.Time) []byte {
	return ccvtypes.AppendMany(
		// append the prefix
		[]byte{SpawnTimeToConsumerIdsKeyPrefix()},
		// append the time
		sdk.FormatTimeBytes(spawnTime),
	)
}

// RemovalTimeToConsumerIdsKeyPrefix returns the key prefix for storing pending chains that are to be removed
func RemovalTimeToConsumerIdsKeyPrefix() byte {
	return mustGetKeyPrefix(RemovalTimeToConsumerIdsKeyName)
}

// RemovalTimeToConsumerIdsKey returns the key prefix for storing the removal times of consumer chains
// that are about to be removed
func RemovalTimeToConsumerIdsKey(removalTime time.Time) []byte {
	return ccvtypes.AppendMany(
		// append the prefix
		[]byte{RemovalTimeToConsumerIdsKeyPrefix()},
		// append the time
		sdk.FormatTimeBytes(removalTime),
	)
}

// ParseTime returns the marshalled time
func ParseTime(prefix byte, bz []byte) (time.Time, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return time.Time{}, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	timestamp, err := sdk.ParseTimeBytes(bz[prefixL:])
	if err != nil {
		return time.Time{}, err
	}
	return timestamp, nil
}

// ProviderConsAddrToOptedInConsumerIdsKey returns the key for storing all the consumer ids that `providerAddr`
// has opted-in to
func ProviderConsAddrToOptedInConsumerIdsKey(providerAddr ProviderConsAddress) []byte {
	return append([]byte{mustGetKeyPrefix(ProviderConsAddrToOptedInConsumerIdsKeyName)}, providerAddr.ToSdkConsAddr().Bytes()...)
}

// ClientIdToConsumerIdKey returns the consumer id that corresponds to this client id
func ClientIdToConsumerIdKey(clientId string) []byte {
	clientIdLength := len(clientId)
	return ccvtypes.AppendMany(
		// Append the prefix
		[]byte{mustGetKeyPrefix(ClientIdToConsumerIdKeyName)},
		// Append the client id length
		sdk.Uint64ToBigEndian(uint64(clientIdLength)),
		// Append the client id
		[]byte(clientId),
	)
}

// NOTE: DO	NOT ADD FULLY DEFINED KEY FUNCTIONS WITHOUT ADDING THEM TO getAllFullyDefinedKeys() IN keys_test.go

//
// End of fully defined key func section
//

//
// Generic helpers section
//

// StringIdAndTsKey returns the key with the following format:
// bytePrefix | len(stringId) | stringId | timestamp
func StringIdAndTsKey(prefix byte, stringId string, timestamp time.Time) []byte {
	return ccvtypes.AppendMany(
		StringIdWithLenKey(prefix, stringId),
		sdk.FormatTimeBytes(timestamp),
	)
}

// ParseStringIdAndTsKey returns the string id and time for a StringIdAndTs key
func ParseStringIdAndTsKey(prefix byte, bz []byte) (string, time.Time, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return "", time.Time{}, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	stringIdL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	stringId := string(bz[prefixL+8 : prefixL+8+int(stringIdL)])
	timestamp, err := sdk.ParseTimeBytes(bz[prefixL+8+int(stringIdL):])
	if err != nil {
		return "", time.Time{}, err
	}
	return stringId, timestamp, nil
}

// StringIdWithLenKey returns the key with the following format:
// bytePrefix | len(stringId) | stringId
func StringIdWithLenKey(prefix byte, stringId string) []byte {
	return ccvtypes.AppendMany(
		// Append the prefix
		[]byte{prefix},
		// Append the string id length
		sdk.Uint64ToBigEndian(uint64(len(stringId))),
		// Append the string id
		[]byte(stringId),
	)
}

// ParseStringIdWithLenKey returns the stringId of a StringIdWithLen key
func ParseStringIdWithLenKey(prefix byte, bz []byte) (string, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return "", fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	stringIdL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	stringId := string(bz[prefixL+8 : prefixL+8+int(stringIdL)])
	return stringId, nil
}

// StringIdAndUintIdKey returns the key with the following format:
// bytePrefix | len(stringId) | stringId | uint64(ID)
func StringIdAndUintIdKey(prefix byte, stringId string, uintId uint64) []byte {
	return ccvtypes.AppendMany(
		StringIdWithLenKey(prefix, stringId),
		sdk.Uint64ToBigEndian(uintId),
	)
}

// ParseStringIdAndUintIdKey returns the string ID and uint ID for a StringIdAndUintId key
func ParseStringIdAndUintIdKey(prefix byte, bz []byte) (string, uint64, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return "", 0, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	stringIdL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	stringId := string(bz[prefixL+8 : prefixL+8+int(stringIdL)])
	uintID := sdk.BigEndianToUint64(bz[prefixL+8+int(stringIdL):])
	return stringId, uintID, nil
}

// StringIdAndConsAddrKey returns the key with the following format:
// bytePrefix | len(stringId) | stringId | ConsAddress
func StringIdAndConsAddrKey(prefix byte, stringId string, addr sdk.ConsAddress) []byte {
	return ccvtypes.AppendMany(
		StringIdWithLenKey(prefix, stringId),
		addr,
	)
}

// ParseStringIdAndConsAddrKey returns the string ID and ConsAddress for a StringIdAndConsAddr key
func ParseStringIdAndConsAddrKey(prefix byte, bz []byte) (string, sdk.ConsAddress, error) {
	expectedPrefix := []byte{prefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return "", nil, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	stringIdL := sdk.BigEndianToUint64(bz[prefixL : prefixL+8])
	stringId := string(bz[prefixL+8 : prefixL+8+int(stringIdL)])
	addr := bz[prefixL+8+int(stringIdL):]
	return stringId, addr, nil
}

//
// End of generic helpers section
//
