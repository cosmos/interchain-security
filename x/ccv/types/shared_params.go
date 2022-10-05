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

func ValidateCCVTimeoutPeriod(i interface{}) error {
	period, ok := i.(time.Duration)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}
	if period <= time.Duration(0) {
		return fmt.Errorf("ibc timeout period is not positive")
	}
	return nil
}
