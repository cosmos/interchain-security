package types

import (
	"fmt"
	"time"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

const (
	// about 2 hr at 7.6 seconds per blocks
	DefaultBlocksPerDistributionTransmission = 1000

	// Default timeout period is 4 weeks to ensure channel doesn't close on timeout
	DefaultCCVTimeoutPeriod = 4 * 7 * 24 * time.Hour
)

// Reflection based keys for params subspace
var (
	KeyEnabled                           = []byte("Enabled")
	KeyBlocksPerDistributionTransmission = []byte("BlocksPerDistributionTransmission")
	KeyDistributionTransmissionChannel   = []byte("DistributionTransmissionChannel")
	KeyProviderFeePoolAddrStr            = []byte("ProviderFeePoolAddrStr")
)

// ParamKeyTable type declaration for parameters
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new consumer parameters with provided arguments
func NewParams(enabled bool, blocksPerDistributionTransmission int64,
	distributionTransmissionChannel, providerFeePoolAddrStr string,
	ccvTimeoutPeriod time.Duration) Params {
	return Params{
		Enabled:                           enabled,
		BlocksPerDistributionTransmission: blocksPerDistributionTransmission,
		DistributionTransmissionChannel:   distributionTransmissionChannel,
		ProviderFeePoolAddrStr:            providerFeePoolAddrStr,
		CcvTimeoutPeriod:                  ccvTimeoutPeriod,
	}
}

// DefaultParams is the default params for the consumer module
func DefaultParams() Params {
	return NewParams(
		false,
		DefaultBlocksPerDistributionTransmission,
		"",
		"",
		DefaultCCVTimeoutPeriod,
	)
}

// Validate all ccv-consumer module parameters
func (p Params) Validate() error {
	return nil
}

// ParamSetPairs implements params.ParamSet
func (p *Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyEnabled, p.Enabled, validateBool),
		paramtypes.NewParamSetPair(KeyBlocksPerDistributionTransmission,
			p.BlocksPerDistributionTransmission, validateInt64),
		paramtypes.NewParamSetPair(KeyDistributionTransmissionChannel,
			p.DistributionTransmissionChannel, validateString),
		paramtypes.NewParamSetPair(KeyProviderFeePoolAddrStr,
			p.ProviderFeePoolAddrStr, validateString),
		paramtypes.NewParamSetPair(ccvtypes.KeyCCVTimeoutPeriod,
			p.CcvTimeoutPeriod, ccvtypes.ValidateCCVTimeoutPeriod),
	}
}

func validateBool(i interface{}) error {
	if _, ok := i.(bool); !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	return nil
}

func validateInt64(i interface{}) error {
	if _, ok := i.(int64); !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	return nil
}

func validateString(i interface{}) error {
	if _, ok := i.(string); !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	return nil
}
