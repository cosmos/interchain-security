package types

import (
	"time"
)

// NewGlobalSlashEntry creates a new GlobalSlashEntry.
func NewGlobalSlashEntry(recvTime time.Time, consumerChainID string,
	ibcSeqNum uint64, providerValConsAddr ProviderConsAddress,
) GlobalSlashEntry {
	return GlobalSlashEntry{
		RecvTime:            recvTime.UTC(), // UTC prevents serialization inconsistencies
		ConsumerChainID:     consumerChainID,
		IbcSeqNum:           ibcSeqNum,
		ProviderValConsAddr: providerValConsAddr.ToSdkConsAddr(),
	}
}
