package types

// Iota generated keys/byte prefixes (as a byte), supports 256 possible values
// DO NOT CHANGE THE ORDER OF THESE CONSTANTS, OR DELETE ANY OF THEM
// YOU CAN ONLY EVER APPEND TO THIS LIST
const (
	PortByteKey byte = iota
	MaturedUnbondingOpsByteKey
	ValidatorSetUpdateIdByteKey
	SlashMeterByteKey
	SlashMeterReplenishTimeCandidateByteKey
	ChainToChannelBytePrefix
	ChannelToChainBytePrefix
	ChainToClientBytePrefix
	MyBadTestPrefix
	InitTimeoutTimestampBytePrefix
	PendingCAPBytePrefix
	PendingCRPBytePrefix
	UnbondingOpBytePrefix
	UnbondingOpIndexBytePrefix
	ValsetUpdateBlockHeightBytePrefix
	ConsumerGenesisBytePrefix
	SlashAcksBytePrefix
	InitChainHeightBytePrefix
	PendingVSCsBytePrefix
	VscSendTimestampBytePrefix
	ThrottledPacketDataSizeBytePrefix
	ThrottledPacketDataBytePrefix
	GlobalSlashEntryBytePrefix
	ConsumerValidatorsBytePrefix
	ValidatorsByConsumerAddrBytePrefix
	KeyAssignmentReplacementsBytePrefix
	ConsumerAddrsToPruneBytePrefix
	SlashLogBytePrefix
	MyTestPrefix
	// NOTE: DO NOT ADD NEW BYTE PREFIXES HERE WITHOUT ADDING THEM TO getAllKeyPrefixes() IN keys_test.go
)
