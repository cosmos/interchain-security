package types

import (
	"fmt"
	sdk "github.com/cosmos/cosmos-sdk/types"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
)

var (
	KeyEnabled                           = []byte("Enabled")
	KeyBlocksPerDistributionTransmission = []byte("BlocksPerDistributionTransmission")
	KeyDistributionTransmissionChannel   = []byte("DistributionTransmissionChannel")
	KeyProviderFeePoolAddrStr            = []byte("ProviderFeePoolAddrStr")
	KeyParamStoreKeyBaseProposerReward   = []byte("BaseProposerReward")
	KeyParamStoreKeyBonusProposerReward  = []byte("BonusProposerReward")
)

// ParamKeyTable type declaration for parameters
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new consumer parameters with provided arguments
func NewParams(enabled bool, blocksPerDistributionTransmission int64,
	distributionTransmissionChannel, providerFeePoolAddrStr string,
	baseProposerReward, bonusProposerReward sdk.Dec) Params {
	return Params{
		Enabled:                           enabled,
		BlocksPerDistributionTransmission: blocksPerDistributionTransmission,
		DistributionTransmissionChannel:   distributionTransmissionChannel,
		ProviderFeePoolAddrStr:            providerFeePoolAddrStr,
		BaseProposerReward:                baseProposerReward,
		BonusProposerReward:               bonusProposerReward,
	}
}

// DefaultParams is the default params for the consumer module
func DefaultParams() Params {
	return NewParams(
		false,
		1000, // about 2 hr at 7.6 seconds per blocks
		"",
		"",
		sdk.NewDecWithPrec(1, 2), // 1%
		sdk.NewDecWithPrec(4, 2), // 4%
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
		paramtypes.NewParamSetPair(KeyParamStoreKeyBaseProposerReward,
			p.BaseProposerReward, validateBaseProposerReward),
		paramtypes.NewParamSetPair(KeyParamStoreKeyBonusProposerReward,
			p.BonusProposerReward, validateBonusProposerReward),
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

func validateBaseProposerReward(i interface{}) error {
	v, ok := i.(sdk.Dec)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}

	if v.IsNil() {
		return fmt.Errorf("base proposer reward must be not nil")
	}
	if v.IsNegative() {
		return fmt.Errorf("base proposer reward must be positive: %s", v)
	}
	if v.GT(sdk.OneDec()) {
		return fmt.Errorf("base proposer reward too large: %s", v)
	}

	return nil
}

func validateBonusProposerReward(i interface{}) error {
	v, ok := i.(sdk.Dec)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}

	if v.IsNil() {
		return fmt.Errorf("bonus proposer reward must be not nil")
	}
	if v.IsNegative() {
		return fmt.Errorf("bonus proposer reward must be positive: %s", v)
	}
	if v.GT(sdk.OneDec()) {
		return fmt.Errorf("bonus proposer reward too large: %s", v)
	}

	return nil
}
