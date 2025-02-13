package interchain

import (
	"cosmos/interchain-security/tests/interchain/chainsuite"
	"fmt"
	"strings"
	"time"

	"cosmossdk.io/math"
	sdkmath "cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v9/modules/core/02-client/types"
	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
)

func msgCreateConsumer(
	chainId string,
	initParams *providertypes.ConsumerInitializationParameters,
	powerParams *providertypes.PowerShapingParameters,
	infractionParams *providertypes.InfractionParameters,
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
		InfractionParameters:     infractionParams,
	}
}

func consumerInitParamsTemplate(spawnTime *time.Time) *providertypes.ConsumerInitializationParameters {
	initParams := &providertypes.ConsumerInitializationParameters{
		InitialHeight:                     clienttypes.NewHeight(1, 1),
		GenesisHash:                       []byte("gen_hash"),
		BinaryHash:                        []byte("bin_hash"),
		UnbondingPeriod:                   1728000000000000,
		CcvTimeoutPeriod:                  2419200000000000,
		TransferTimeoutPeriod:             3600000000000,
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

func infractionParamsTemplate() *providertypes.InfractionParameters {
	return &providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  1200 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(7, 2), // 0.07
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  2400 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(8, 2), // 0.08
		},
	}
}

func defaultInfractionParams() *providertypes.InfractionParameters {
	return &providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  time.Duration(1<<63 - 1),        // the largest value a time.Duration can hold 9223372036854775807 (approximately 292 years)
			SlashFraction: math.LegacyNewDecWithPrec(5, 2), // 0.05
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  chainsuite.DowntimeJailDuration,
			SlashFraction: math.LegacyNewDec(0), // no slashing for downtime on the consumer
		},
	}
}

func convertJsonToInfractionParameters(jsonParams chainsuite.InfractionParams) *providertypes.InfractionParameters {
	doubleSignJailDuration, _ := time.ParseDuration(jsonParams.DoubleSign.JailDuration)
	downtimeJailDuration, _ := time.ParseDuration(jsonParams.Downtime.JailDuration)

	return &providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			SlashFraction: math.LegacyMustNewDecFromStr(jsonParams.DoubleSign.SlashFraction),
			JailDuration:  doubleSignJailDuration,
		},
		Downtime: &providertypes.SlashJailParameters{
			SlashFraction: math.LegacyMustNewDecFromStr(jsonParams.Downtime.SlashFraction),
			JailDuration:  downtimeJailDuration,
		},
	}
}

func StrToSDKInt(s string) (sdkmath.Int, error) {
	s, _, _ = strings.Cut(s, ".")
	i, ok := sdkmath.NewIntFromString(s)
	if !ok {
		return sdkmath.Int{}, fmt.Errorf("s: %s", s)
	}
	return i, nil
}
