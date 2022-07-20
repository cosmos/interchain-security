package types

const (
	// ModuleName defines the CCV module name
	ModuleName = "CCV"

	// Version defines the current version the IBC CCV provider and consumer
	// module supports
	Version = "1"

	RouterKey = ModuleName
)

// Iota generated keys/byte prefixes (as a byte), supports 256 possible values
const (
	// ChannelStatusKeyPrefix is the byte prefix for storing the validation status of the CCV channel
	ChannelStatusBytePrefix byte = iota
)

func ChannelStatusPrefix() []byte {
	return []byte{ChannelStatusBytePrefix}
}

// ChannelStatusKey returns the key under which the Status of a consumer chain is stored.
func ChannelStatusKey(channelID string) []byte {
	return append(ChannelStatusPrefix(), []byte("/"+channelID)...)
}
