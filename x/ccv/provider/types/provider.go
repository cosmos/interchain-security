package types

import (
	"context"
	"time"

	"cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v10/modules/core/02-client/types"

	ccv "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

func DefaultConsumerInitializationParameters() ConsumerInitializationParameters {
	return ConsumerInitializationParameters{
		InitialHeight: clienttypes.Height{
			RevisionNumber: 1,
			RevisionHeight: 1,
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

func DefaultConsumerInfractionParameters(ctx context.Context, slashingKeeper ccv.SlashingKeeper) (InfractionParameters, error) {
	jailDuration, err := slashingKeeper.DowntimeJailDuration(ctx)
	if err != nil {
		return InfractionParameters{}, err
	}

	doubleSignSlashingFraction, err := slashingKeeper.SlashFractionDoubleSign(ctx)
	if err != nil {
		return InfractionParameters{}, err
	}

	return InfractionParameters{
		DoubleSign: &SlashJailParameters{
			JailDuration:  time.Duration(1<<63 - 1), // the largest value a time.Duration can hold 9223372036854775807 (approximately 292 years)
			SlashFraction: doubleSignSlashingFraction,
			Tombstone:     true,
		},
		Downtime: &SlashJailParameters{
			JailDuration:  jailDuration,
			SlashFraction: math.LegacyNewDec(0),
			Tombstone:     false,
		},
	}, nil
}
