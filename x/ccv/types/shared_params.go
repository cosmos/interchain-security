package types

import (
	fmt "fmt"
	"time"

	ibchost "github.com/cosmos/ibc-go/v7/modules/core/24-host"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
)

const (
	// Default timeout period is 4 weeks to ensure channel doesn't close on timeout
	DefaultCCVTimeoutPeriod = 4 * 7 * 24 * time.Hour
)

var KeyCCVTimeoutPeriod = []byte("CcvTimeoutPeriod")

func ValidateDuration(i interface{}) error {
	period, ok := i.(time.Duration)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	if period <= time.Duration(0) {
		return fmt.Errorf("duration must be positive")
	}
	return nil
}

func ValidateBool(i interface{}) error {
	if _, ok := i.(bool); !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	return nil
}

func ValidateInt64(i interface{}) error {
	if _, ok := i.(int64); !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	return nil
}

func ValidatePositiveInt64(i interface{}) error {
	if err := ValidateInt64(i); err != nil {
		return err
	}
	if i.(int64) <= int64(0) {
		return fmt.Errorf("int must be positive")
	}
	return nil
}

func ValidateString(i interface{}) error {
	if _, ok := i.(string); !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	return nil
}

func ValidateDistributionTransmissionChannel(i interface{}) error {
	// Accept empty string as valid, since this means a new
	// distribution transmission channel will be created
	if i == "" {
		return nil
	}
	// Otherwise validate as usual for a channelID
	return ValidateChannelIdentifier(i)
}

func ValidateChannelIdentifier(i interface{}) error {
	value, ok := i.(string)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	return ibchost.ChannelIdentifierValidator(value)
}

func ValidateBech32(i interface{}) error {
	value, ok := i.(string)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	_, err := sdktypes.AccAddressFromBech32(value)
	return err
}

func ValidateStringFraction(i interface{}) error {
	str, ok := i.(string)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	dec, err := sdktypes.NewDecFromStr(str)
	if err != nil {
		return err
	}
	if dec.IsNegative() {
		return fmt.Errorf("param cannot be negative, got %s", str)
	}
	if dec.Sub(sdktypes.NewDec(1)).IsPositive() {
		return fmt.Errorf("param cannot be greater than 1, got %s", str)
	}
	return nil
}

func CalculateTrustPeriod(unbondingPeriod time.Duration, defaultTrustPeriodFraction string) (time.Duration, error) {
	trustDec, err := sdktypes.NewDecFromStr(defaultTrustPeriodFraction)
	if err != nil {
		return time.Duration(0), err
	}
	trustPeriod := time.Duration(trustDec.MulInt64(unbondingPeriod.Nanoseconds()).TruncateInt64())

	return trustPeriod, nil
}
