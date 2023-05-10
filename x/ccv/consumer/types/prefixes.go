package types

// Iota generated keys/key prefixes (as a byte), supports 256 possible values
// DO NOT CHANGE THE ORDER OF THESE CONSTANTS, OR DELETE ANY OF THEM
// YOU CAN ONLY EVER APPEND TO THIS LIST
// Iota generated keys/key prefixes (as a byte), supports 256 possible values
const (
	PortByteKey byte = iota
	LastDistributionTransmissionByteKey
	UnbondingTimeByteKey
	ProviderClientByteKey
	ProviderChannelByteKey
	PendingChangesByteKey
	PendingDataPacketsByteKey
	PreCCVByteKey
	InitialValSetByteKey
	InitGenesisHeightByteKey
	SmallestNonOptOutPowerByteKey
	StandaloneTransferChannelIDByteKey
	PrevStandaloneChainByteKey
	HistoricalInfoBytePrefix
	PacketMaturityTimeBytePrefix
	HeightValsetUpdateIDBytePrefix
	OutstandingDowntimeBytePrefix
	CrossChainValidatorBytePrefix

	// NOTE: DO NOT ADD NEW BYTE PREFIXES HERE WITHOUT ADDING THEM TO getAllKeyPrefixes() IN keys_test.go
)
