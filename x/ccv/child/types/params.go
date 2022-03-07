package types

import (
	"fmt"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
)

var (
	KeyEnabled                           = []byte("Enabled")
	KeyBlocksPerDistributionTransmission = []byte("BlocksPerDistributionTransmission")
	KeyProviderFeePoolAddrStr            = []byte("ProviderFeePoolAddrStr")
	KeyDistributionTransmissionChannel   = []byte("DistributionTransmissionChannel")
)

// ParamKeyTable type declaration for parameters
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new child parameters with provided arguments
func NewParams(enabled bool) Params {
	return Params{
		Enabled:                           enabled,
		BlocksPerDistributionTransmission: 0,
		ProviderFeePoolAddrStr:            "",
		DistributionTransmissionChannel:   "",
	}
}

// DefaultParams is the default params for the child module
func DefaultParams() Params {
	return NewParams(false)
}

// Validate all ccv-child module parameters
func (p Params) Validate() error {
	return nil
}

// ParamSetPairs implements params.ParamSet
func (p *Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyEnabled, p.Enabled, validateBool),
		paramtypes.NewParamSetPair(KeyBlocksPerDistributionTransmission,
			p.BlocksPerDistributionTransmission, validateInt64),
		paramtypes.NewParamSetPair(KeyProviderFeePoolAddrStr,
			p.ProviderFeePoolAddrStr, validateString),
		paramtypes.NewParamSetPair(KeyDistributionTransmissionChannel,
			p.DistributionTransmissionChannel, validateString),
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
