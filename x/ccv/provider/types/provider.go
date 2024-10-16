package types

import (
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"

	ccv "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

func DefaultConsumerInitializationParameters() ConsumerInitializationParameters {
	return ConsumerInitializationParameters{
		InitialHeight: clienttypes.Height{
			RevisionNumber: 1,
			RevisionHeight: 0,
		},
		GenesisHash:                       []byte{},
		BinaryHash:                        []byte{},
		SpawnTime:                         time.Time{},
		UnbondingPeriod:                   ccv.DefaultConsumerUnbondingPeriod,
		CcvTimeoutPeriod:                  ccv.DefaultCCVTimeoutPeriod,
		TransferTimeoutPeriod:             ccv.DefaultTransferTimeoutPeriod,
		ConsumerRedistributionFraction:    ccv.DefaultConsumerRedistributeFrac,
		BlocksPerDistributionTransmission: ccv.DefaultBlocksPerDistributionTransmission,
		HistoricalEntries:                 ccv.DefaultHistoricalEntries,
		DistributionTransmissionChannel:   "",
	}
}
