package types

import (
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
)

// NewGlobalSlashEntry creates a new GlobalSlashEntry.
func NewGlobalSlashEntry(recvTime time.Time, consumerChainID string,
	ibcSeqNum uint64, providerValConsAddr sdktypes.ConsAddress,
) GlobalSlashEntry {
	return GlobalSlashEntry{
		RecvTime:            recvTime.UTC(), // UTC prevents serialization inconsistencies
		ConsumerChainID:     consumerChainID,
		IbcSeqNum:           ibcSeqNum,
		ProviderValConsAddr: providerValConsAddr,
	}
}
