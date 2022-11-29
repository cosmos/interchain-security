package v1

// Iota generated keys/key prefixes (as a byte), supports 256 possible values
const (
	// PortByteKey defines the byte key to store the port ID in store
	PortByteKey byte = iota

	// LastDistributionTransmissionByteKey defines the byte key to store the last distribution transmission
	LastDistributionTransmissionByteKey

	// UnbondingTimeKeyString is the byte key for storing the unbonding period
	UnbondingTimeByteKey

	// ProviderClientKeyString is the byte key for storing the clientID of the provider client
	ProviderClientByteKey

	// ProviderChannelKeyString is the byte key for storing the channelID of the CCV channel
	ProviderChannelByteKey

	// PendingChangesKeyString is the byte key that will store any pending validator set changes
	// received over CCV channel but not yet flushed over ABCI
	PendingChangesByteKey

	// HistoricalInfoKey is the byte prefix that will store the historical info for a given height
	HistoricalInfoBytePrefix

	// PacketMaturityTimePrefix is the byte prefix that will store maturity time for each received VSC packet
	PacketMaturityTimeBytePrefix

	// HeightValsetUpdateIDPrefix is the byte prefix that will store the mapping from block height to valset update ID
	HeightValsetUpdateIDBytePrefix

	// OutstandingDowntimePrefix is the byte prefix that will store the validators outstanding downtime by consensus address
	OutstandingDowntimeBytePrefix

	// PendingSlashRequestsPrefix is the byte prefix that will store a list of slash request that must be sent
	// to the provider chain once the CCV channel is established
	PendingSlashRequestsBytePrefix

	// CrossChainValidatorPrefix is the byte prefix that will store cross-chain validators by consensus address
	CrossChainValidatorBytePrefix
)