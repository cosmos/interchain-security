package types

import (
	"time"
)

// NewGlobalSlashEntry creates a new GlobalSlashEntry.
func NewGlobalSlashEntry(recvTime time.Time, consumerChainID string,
<<<<<<< HEAD
	ibcSeqNum uint64, providerValConsAddr sdktypes.ConsAddress,
) GlobalSlashEntry {
=======
	ibcSeqNum uint64, providerValConsAddr ProviderConsAddress) GlobalSlashEntry {
>>>>>>> origin/main
	return GlobalSlashEntry{
		RecvTime:            recvTime.UTC(), // UTC prevents serialization inconsistencies
		ConsumerChainID:     consumerChainID,
		IbcSeqNum:           ibcSeqNum,
		ProviderValConsAddr: &providerValConsAddr,
	}
}
