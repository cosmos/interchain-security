package types

import (
	fmt "fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

const (
	// about 2 hr at 7.6 seconds per blocks
	DefaultBlocksPerDistributionTransmission = 1000

	// 1 week
	DefaultTransferTimeoutPeriod = 1 * 7 * 24 * time.Hour

	// The fraction of tokens allocated to the consumer redistribution address
	// during distribution events. The fraction is a string representing a
	// decimal number. For example "0.75" would represent 75%.
	DefaultConsumerRedistributeFrac = "0.75"

	// Default number of historical info entries to persist in store
	DefaultNumHistoricalEntries = 10000
)

// Reflection based keys for params subspace
var (
	KeyEnabled                           = []byte("Enabled")
	KeyBlocksPerDistributionTransmission = []byte("BlocksPerDistributionTransmission")
	KeyDistributionTransmissionChannel   = []byte("DistributionTransmissionChannel")
	KeyProviderFeePoolAddrStr            = []byte("ProviderFeePoolAddrStr")
	KeyTransferTimeoutPeriod             = []byte("TransferTimeoutPeriod")
	KeyConsumerRedistributionFrac        = []byte("ConsumerRedistributionFraction")
	KeyNumHistoricalEntries              = []byte("NumHistoricalEntries")
)

// ParamKeyTable type declaration for parameters
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new consumer parameters with provided arguments
func NewParams(enabled bool, blocksPerDistributionTransmission int64,
	distributionTransmissionChannel, providerFeePoolAddrStr string,
	ccvTimeoutPeriod time.Duration, transferTimeoutPeriod time.Duration,
	consumerRedistributionFraction string, numHistoricalEntries int64) Params {
	return Params{
		Enabled:                           enabled,
		BlocksPerDistributionTransmission: blocksPerDistributionTransmission,
		DistributionTransmissionChannel:   distributionTransmissionChannel,
		ProviderFeePoolAddrStr:            providerFeePoolAddrStr,
		CcvTimeoutPeriod:                  ccvTimeoutPeriod,
		TransferTimeoutPeriod:             transferTimeoutPeriod,
		// TODO: Find a way to make sure fraction is valid, or don't do that here?
		ConsumerRedistributionFraction: consumerRedistributionFraction,
		NumHistoricalEntries:           numHistoricalEntries,
	}
}

// DefaultParams is the default params for the consumer module
func DefaultParams() Params {
	return NewParams(
		false,
		DefaultBlocksPerDistributionTransmission,
		"",
		"",
		ccvtypes.DefaultCCVTimeoutPeriod,
		DefaultTransferTimeoutPeriod,
		DefaultConsumerRedistributeFrac,
		DefaultNumHistoricalEntries,
	)
}

// Validate all ccv-consumer module parameters
// TODO: Unit tests similar to provider
func (p Params) Validate() error {
	if err := ccvtypes.ValidateBool(p.Enabled); err != nil {
		return err
	}
	if err := ccvtypes.ValidatePositiveInt64(p.BlocksPerDistributionTransmission); err != nil {
		return err
	}
	// TODO: Is it acceptable if string is empty? Defaults say yes
	if err := ccvtypes.ValidateString(p.DistributionTransmissionChannel); err != nil {
		return err
	}
	// TODO: Is it acceptable if string is empty? Defaults say yes
	if err := ccvtypes.ValidateString(p.ProviderFeePoolAddrStr); err != nil {
		return err
	}
	if err := ccvtypes.ValidateDuration(p.CcvTimeoutPeriod); err != nil {
		return err
	}
	if err := ccvtypes.ValidateDuration(p.TransferTimeoutPeriod); err != nil {
		return err
	}
	if err := validateConsumerRedistributionFraction(p.ConsumerRedistributionFraction); err != nil {
		return err
	}
	if err := ccvtypes.ValidatePositiveInt64(p.NumHistoricalEntries); err != nil {
		return err
	}
	return nil
}

func validateConsumerRedistributionFraction(i interface{}) error {
	str, ok := i.(string)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	dec, err := sdk.NewDecFromStr(str)
	if err != nil {
		return err
	}
	if !dec.IsPositive() {
		return fmt.Errorf("consumer redistribution fraction is not positive")
	}
	if dec.Sub(sdk.NewDec(1)).IsPositive() {
		return fmt.Errorf("consumer redistribution fraction cannot be above 1.0")
	}
	return nil
}

// ParamSetPairs implements params.ParamSet
func (p *Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyEnabled, p.Enabled, ccvtypes.ValidateBool),
		paramtypes.NewParamSetPair(KeyBlocksPerDistributionTransmission,
			p.BlocksPerDistributionTransmission, ccvtypes.ValidatePositiveInt64),
		paramtypes.NewParamSetPair(KeyDistributionTransmissionChannel,
			p.DistributionTransmissionChannel, ccvtypes.ValidateString),
		paramtypes.NewParamSetPair(KeyProviderFeePoolAddrStr,
			p.ProviderFeePoolAddrStr, ccvtypes.ValidateString),
		paramtypes.NewParamSetPair(ccvtypes.KeyCCVTimeoutPeriod,
			p.CcvTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeyTransferTimeoutPeriod,
			p.TransferTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeyConsumerRedistributionFrac,
			p.ConsumerRedistributionFraction, validateConsumerRedistributionFraction),
		paramtypes.NewParamSetPair(KeyNumHistoricalEntries,
			p.NumHistoricalEntries, ccvtypes.ValidatePositiveInt64),
	}
}
