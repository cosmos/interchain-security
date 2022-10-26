package types

import (
	"time"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// The provider's concept of a slash packet received from a consumer chain.
type SlashPacket struct {
	// Block time that slash packet was received by provider chain.
	RecvTime time.Time
	// The consumer that sent the packet.
	ConsumerChainID string
	// The data sent over the wire from consumer to provider.
	Data ccv.SlashPacketData
}

// NewSlashPacket creates a new SlashPacket.
func NewSlashPacket(recvTime time.Time, consumerChainID string, data ccv.SlashPacketData) SlashPacket {
	return SlashPacket{
		RecvTime:        recvTime.UTC(), // UTC prevents serialization inconsistencies
		ConsumerChainID: consumerChainID,
		Data:            data,
	}
}
