package types

import (
	fmt "fmt"
	"time"
)

const (
	// Default timeout period is 4 weeks to ensure channel doesn't close on timeout
	DefaultCCVTimeoutPeriod = 4 * 7 * 24 * time.Hour
)

var (
	KeyCCVTimeoutPeriod = []byte("CcvTimeoutPeriod")
)

func ValidateDuration(i interface{}) error {
	period, ok := i.(time.Duration)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	if period <= time.Duration(0) {
		return fmt.Errorf("ibc timeout period is not positive")
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
