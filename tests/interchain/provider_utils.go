package interchain

import (
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
)

func msgCreateConsumer(
	chainId string,
	initParams *providertypes.ConsumerInitializationParameters,
	powerParams *providertypes.PowerShapingParameters,
	submiter string) *providertypes.MsgCreateConsumer {
	consumerMetadata := providertypes.ConsumerMetadata{
		Name:        chainId,
		Description: "description",
		Metadata:    "metadata",
	}

	return &providertypes.MsgCreateConsumer{
		Submitter:                submiter,
		ChainId:                  chainId,
		Metadata:                 consumerMetadata,
		InitializationParameters: initParams,
		PowerShapingParameters:   powerParams,
	}
}

func consumerInitParamsTemplate(spawnTime *time.Time) *providertypes.ConsumerInitializationParameters {
	initParams := &providertypes.ConsumerInitializationParameters{
		InitialHeight:                     clienttypes.NewHeight(0, 1),
		GenesisHash:                       []byte("gen_hash"),
		BinaryHash:                        []byte("bin_hash"),
		UnbondingPeriod:                   10 * time.Second,
		CcvTimeoutPeriod:                  time.Duration(100000000000),
		TransferTimeoutPeriod:             time.Duration(100000000000),
		ConsumerRedistributionFraction:    "0.75",
		BlocksPerDistributionTransmission: 10,
		HistoricalEntries:                 10000,
		DistributionTransmissionChannel:   "",
	}

	if spawnTime != nil {
		initParams.SpawnTime = *spawnTime
	}

	return initParams
}

func powerShapingParamsTemplate() *providertypes.PowerShapingParameters {
	return &providertypes.PowerShapingParameters{
		Top_N:              0,
		ValidatorsPowerCap: 0,
		ValidatorSetCap:    50,
		Allowlist:          []string{},
		Denylist:           []string{},
		MinStake:           1000,
		AllowInactiveVals:  true,
	}
}
