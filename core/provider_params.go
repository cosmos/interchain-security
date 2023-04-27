package core

import (
	"fmt"
	"time"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v4/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
)

const (
	// DefaultMaxClockDrift defines how much new (untrusted) header's Time can drift into the future.
	// This default is only used in the default template client param.
	DefaultMaxClockDrift = 10 * time.Second

	// DefaultTrustingPeriodFraction is the default fraction used to compute TrustingPeriod
	// as UnbondingPeriod * TrustingPeriodFraction
	DefaultTrustingPeriodFraction = "0.66"

	// DefaultInitTimeoutPeriod defines the init timeout period
	DefaultInitTimeoutPeriod = 7 * 24 * time.Hour

	// DefaultVscTimeoutPeriod defines the VSC timeout period
	DefaultVscTimeoutPeriod = 5 * 7 * 24 * time.Hour

	// DefaultSlashMeterReplenishPeriod defines the default period for which the slash gas meter is replenished
	DefaultSlashMeterReplenishPeriod = time.Hour

	// DefaultSlashMeterReplenishFraction defines the default fraction of total voting power
	// that is replenished to the slash meter every replenish period. This param also serves as a maximum
	// fraction of total voting power that the slash meter can hold.
	DefaultSlashMeterReplenishFraction = "0.05"

	// DefaultMaxThrottledPackets defines the default amount of throttled slash or vsc matured packets
	// that can be queued for a single consumer before the provider chain halts.
	DefaultMaxThrottledPackets = 100000
)

// Reflection based keys for params subspace
var (
	KeyTemplateClient              = []byte("TemplateClient")
	KeyTrustingPeriodFraction      = []byte("TrustingPeriodFraction")
	KeyInitTimeoutPeriod           = []byte("InitTimeoutPeriod")
	KeyVscTimeoutPeriod            = []byte("VscTimeoutPeriod")
	KeySlashMeterReplenishPeriod   = []byte("SlashMeterReplenishPeriod")
	KeySlashMeterReplenishFraction = []byte("SlashMeterReplenishFraction")
	KeyMaxThrottledPackets         = []byte("MaxThrottledPackets")
)

// ProviderParamKeyTable returns a key table with the necessary registered provider params
func ProviderParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&ProviderParams{})
}

// NewParams creates new provider parameters with provided arguments
func NewProviderParams(
	cs *ibctmtypes.ClientState,
	trustingPeriodFraction string,
	ccvTimeoutPeriod time.Duration,
	initTimeoutPeriod time.Duration,
	vscTimeoutPeriod time.Duration,
	slashMeterReplenishPeriod time.Duration,
	slashMeterReplenishFraction string,
	maxThrottledPackets int64,
) ProviderParams {
	return ProviderParams{
		TemplateClient:              cs,
		TrustingPeriodFraction:      trustingPeriodFraction,
		CcvTimeoutPeriod:            ccvTimeoutPeriod,
		InitTimeoutPeriod:           initTimeoutPeriod,
		VscTimeoutPeriod:            vscTimeoutPeriod,
		SlashMeterReplenishPeriod:   slashMeterReplenishPeriod,
		SlashMeterReplenishFraction: slashMeterReplenishFraction,
		MaxThrottledPackets:         maxThrottledPackets,
	}
}

// DefaultProviderParams is the default params for the provider module
func DefaultProviderParams() ProviderParams {
	// create default client state with chainID, trusting period, unbonding period, and initial height zeroed out.
	// these fields will be populated during proposal handler.
	return NewProviderParams(
		ibctmtypes.NewClientState(
			"", // chainID
			ibctmtypes.DefaultTrustLevel,
			0, // trusting period
			0, // unbonding period
			DefaultMaxClockDrift,
			clienttypes.Height{}, // latest(initial) height
			commitmenttypes.GetSDKSpecs(),
			[]string{"upgrade", "upgradedIBCState"},
			true,
			true,
		),
		DefaultTrustingPeriodFraction,
		DefaultCCVTimeoutPeriod,
		DefaultInitTimeoutPeriod,
		DefaultVscTimeoutPeriod,
		DefaultSlashMeterReplenishPeriod,
		DefaultSlashMeterReplenishFraction,
		DefaultMaxThrottledPackets,
	)
}

// Validate all ccv-provider module parameters
func (p ProviderParams) Validate() error {
	if p.TemplateClient == nil {
		return fmt.Errorf("template client is nil")
	}
	if err := validateTemplateClient(*p.TemplateClient); err != nil {
		return err
	}
	if err := ValidateStringFraction(p.TrustingPeriodFraction); err != nil {
		return fmt.Errorf("trusting period fraction is invalid: %s", err)
	}
	if err := ValidateDuration(p.CcvTimeoutPeriod); err != nil {
		return fmt.Errorf("ccv timeout period is invalid: %s", err)
	}
	if err := ValidateDuration(p.InitTimeoutPeriod); err != nil {
		return fmt.Errorf("init timeout period is invalid: %s", err)
	}
	if err := ValidateDuration(p.VscTimeoutPeriod); err != nil {
		return fmt.Errorf("vsc timeout period is invalid: %s", err)
	}
	if err := ValidateDuration(p.SlashMeterReplenishPeriod); err != nil {
		return fmt.Errorf("slash meter replenish period is invalid: %s", err)
	}
	if err := ValidateStringFraction(p.SlashMeterReplenishFraction); err != nil {
		return fmt.Errorf("slash meter replenish fraction is invalid: %s", err)
	}
	if err := ValidatePositiveInt64(p.MaxThrottledPackets); err != nil {
		return fmt.Errorf("max throttled packets is invalid: %s", err)
	}
	return nil
}

// ParamSetPairs implements params.ParamSet
func (p *ProviderParams) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyTemplateClient, p.TemplateClient, validateTemplateClient),
		paramtypes.NewParamSetPair(KeyTrustingPeriodFraction, p.TrustingPeriodFraction, ValidateStringFraction),
		paramtypes.NewParamSetPair(KeyCCVTimeoutPeriod, p.CcvTimeoutPeriod, ValidateDuration),
		paramtypes.NewParamSetPair(KeyInitTimeoutPeriod, p.InitTimeoutPeriod, ValidateDuration),
		paramtypes.NewParamSetPair(KeyVscTimeoutPeriod, p.VscTimeoutPeriod, ValidateDuration),
		paramtypes.NewParamSetPair(KeySlashMeterReplenishPeriod, p.SlashMeterReplenishPeriod, ValidateDuration),
		paramtypes.NewParamSetPair(KeySlashMeterReplenishFraction, p.SlashMeterReplenishFraction, ValidateStringFraction),
		paramtypes.NewParamSetPair(KeyMaxThrottledPackets, p.MaxThrottledPackets, ValidatePositiveInt64),
	}
}

func validateTemplateClient(i interface{}) error {
	cs, ok := i.(ibctmtypes.ClientState)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T, expected: %T", i, ibctmtypes.ClientState{})
	}

	// copy clientstate to prevent changing original pointer
	copiedClient := cs

	// populate zeroed fields with valid fields
	copiedClient.ChainId = "chainid"

	trustPeriod, err := CalculateTrustPeriod(DefaultConsumerUnbondingPeriod, DefaultTrustingPeriodFraction)
	if err != nil {
		return fmt.Errorf("invalid TrustPeriodFraction: %T", err)
	}
	copiedClient.TrustingPeriod = trustPeriod

	copiedClient.UnbondingPeriod = DefaultConsumerUnbondingPeriod
	copiedClient.LatestHeight = clienttypes.NewHeight(0, 1)

	if err := copiedClient.Validate(); err != nil {
		return err
	}
	return nil
}
