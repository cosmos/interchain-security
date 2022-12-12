package types

import (
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
)

// A persisted queue entry indicating that a slash packet data instance needs to be handled.
// This struct belongs in the "global" queue, to coordinate slash packet handling times between consumers.
type GlobalSlashEntry struct {
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

// NewGlobalSlashEntry creates a new GlobalSlashEntry.
func NewGlobalSlashEntry(recvTime time.Time, consumerChainID string,
	ibcSeqNum uint64, providerValConsAddr sdktypes.ConsAddress) GlobalSlashEntry {
	return GlobalSlashEntry{
		RecvTime:            recvTime.UTC(), // UTC prevents serialization inconsistencies
		ConsumerChainID:     consumerChainID,
		IbcSeqNum:           ibcSeqNum,
		ProviderValConsAddr: providerValConsAddr,
	}
}
