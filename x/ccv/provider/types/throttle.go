package types

import (
	"time"
)

// A persisted queue entry indicating that a slash packet data instance needs to be handled
type SlashPacketEntry struct {
	// Block time that slash packet was received by provider chain.
	RecvTime time.Time
	// The consumer that sent the packet.
	ConsumerChainID string
	// The byte address of the validator being slashed.
	ValAddr []byte
}

// NewSlashPacketEntry creates a new SlashPacketEntry.
func NewSlashPacketEntry(recvTime time.Time, consumerChainID string, valAddr []byte) SlashPacketEntry {
	return SlashPacketEntry{
		RecvTime:        recvTime.UTC(), // UTC prevents serialization inconsistencies
		ConsumerChainID: consumerChainID,
		ValAddr:         valAddr,
	}
}
