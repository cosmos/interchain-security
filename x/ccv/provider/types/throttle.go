package types

import (
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
)

// A persisted queue entry indicating that a slash packet data instance needs to be handled
type SlashPacketEntry struct {
	// Block time that slash packet was received by provider chain.
	// This field is used for store key iteration ordering.
	RecvTime time.Time
	// The consumer that sent the packet.
	ConsumerChainID string
	// The IBC sequence number of the recv packet.
	// This field is used in the store key to ensure uniqueness.
	IbcSeqNum uint64
	// The provider's consensus address of the validator being slashed.
	// This field is used to obtain validator power in HandlePendingSlashPackets.
	// It is not used in the store key, but is persisted in value bytes,
	// see QueuePendingSlashPacketEntry.
	ProviderValConsAddr sdktypes.ConsAddress
}

// NewSlashPacketEntry creates a new SlashPacketEntry.
func NewSlashPacketEntry(recvTime time.Time, consumerChainID string,
	ibcSeqNum uint64, providerValConsAddr sdktypes.ConsAddress) SlashPacketEntry {
	return SlashPacketEntry{
		RecvTime:            recvTime.UTC(), // UTC prevents serialization inconsistencies
		ConsumerChainID:     consumerChainID,
		IbcSeqNum:           ibcSeqNum,
		ProviderValConsAddr: providerValConsAddr,
	}
}
