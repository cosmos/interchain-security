package types

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v7/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"

	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
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
	KeyTemplateClient                     = []byte("TemplateClient")
	KeyTrustingPeriodFraction             = []byte("TrustingPeriodFraction")
	KeyInitTimeoutPeriod                  = []byte("InitTimeoutPeriod")
	KeyVscTimeoutPeriod                   = []byte("VscTimeoutPeriod")
	KeySlashMeterReplenishPeriod          = []byte("SlashMeterReplenishPeriod")
	KeySlashMeterReplenishFraction        = []byte("SlashMeterReplenishFraction")
	KeyMaxThrottledPackets                = []byte("MaxThrottledPackets")
	KeyConsumerRewardDenomRegistrationFee = []byte("ConsumerRewardDenomRegistrationFee")
)

// ParamKeyTable returns a key table with the necessary registered provider params
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new provider parameters with provided arguments
func NewParams(
	cs *ibctmtypes.ClientState,
	trustingPeriodFraction string,
	ccvTimeoutPeriod time.Duration,
	initTimeoutPeriod time.Duration,
	vscTimeoutPeriod time.Duration,
	slashMeterReplenishPeriod time.Duration,
	slashMeterReplenishFraction string,
	maxThrottledPackets int64,
	consumerRewardDenomRegistrationFee sdk.Coin,
) Params {
	return Params{
		TemplateClient:                     cs,
		TrustingPeriodFraction:             trustingPeriodFraction,
		CcvTimeoutPeriod:                   ccvTimeoutPeriod,
		InitTimeoutPeriod:                  initTimeoutPeriod,
		VscTimeoutPeriod:                   vscTimeoutPeriod,
		SlashMeterReplenishPeriod:          slashMeterReplenishPeriod,
		SlashMeterReplenishFraction:        slashMeterReplenishFraction,
		MaxThrottledPackets:                maxThrottledPackets,
		ConsumerRewardDenomRegistrationFee: consumerRewardDenomRegistrationFee,
	}
}

// DefaultParams is the default params for the provider module
func DefaultParams() Params {
	// create default client state with chainID, trusting period, unbonding period, and initial height zeroed out.
	// these fields will be populated during proposal handler.
	return NewParams(
		ibctmtypes.NewClientState(
			"", // chainID
			ibctmtypes.DefaultTrustLevel,
			0, // trusting period
			0, // unbonding period
			DefaultMaxClockDrift,
			clienttypes.Height{}, // latest(initial) height
			commitmenttypes.GetSDKSpecs(),
			[]string{"upgrade", "upgradedIBCState"},
		),
		DefaultTrustingPeriodFraction,
		ccvtypes.DefaultCCVTimeoutPeriod,
		DefaultInitTimeoutPeriod,
		DefaultVscTimeoutPeriod,
		DefaultSlashMeterReplenishPeriod,
		DefaultSlashMeterReplenishFraction,
		DefaultMaxThrottledPackets,
		// Defining this inline because it's not possible to define a constant of type sdk.Coin.
		// Following the pattern from cosmos-sdk/staking/types/params.go
		sdk.Coin{
			Denom:  sdk.DefaultBondDenom,
			Amount: sdk.NewInt(10000000),
		},
	)
}

// Validate all ccv-provider module parameters
func (p Params) Validate() error {
	if p.TemplateClient == nil {
		return fmt.Errorf("template client is nil")
	}
	if err := ValidateTemplateClient(*p.TemplateClient); err != nil {
		return err
	}
	if err := ccvtypes.ValidateStringFraction(p.TrustingPeriodFraction); err != nil {
		return fmt.Errorf("trusting period fraction is invalid: %s", err)
	}
	if err := ccvtypes.ValidateDuration(p.CcvTimeoutPeriod); err != nil {
		return fmt.Errorf("ccv timeout period is invalid: %s", err)
	}
	if err := ccvtypes.ValidateDuration(p.InitTimeoutPeriod); err != nil {
		return fmt.Errorf("init timeout period is invalid: %s", err)
	}
	if err := ccvtypes.ValidateDuration(p.VscTimeoutPeriod); err != nil {
		return fmt.Errorf("vsc timeout period is invalid: %s", err)
	}
	if err := ccvtypes.ValidateDuration(p.SlashMeterReplenishPeriod); err != nil {
		return fmt.Errorf("slash meter replenish period is invalid: %s", err)
	}
	if err := ccvtypes.ValidateStringFraction(p.SlashMeterReplenishFraction); err != nil {
		return fmt.Errorf("slash meter replenish fraction is invalid: %s", err)
	}
	if err := ccvtypes.ValidatePositiveInt64(p.MaxThrottledPackets); err != nil {
		return fmt.Errorf("max throttled packets is invalid: %s", err)
	}
	if err := ValidateCoin(p.ConsumerRewardDenomRegistrationFee); err != nil {
		return fmt.Errorf("consumer reward denom registration fee is invalid: %s", err)
	}
	return nil
}

// ParamSetPairs implements params.ParamSet
func (p *Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyTemplateClient, p.TemplateClient, ValidateTemplateClient),
		paramtypes.NewParamSetPair(KeyTrustingPeriodFraction, p.TrustingPeriodFraction, ccvtypes.ValidateStringFraction),
		paramtypes.NewParamSetPair(ccvtypes.KeyCCVTimeoutPeriod, p.CcvTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeyInitTimeoutPeriod, p.InitTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeyVscTimeoutPeriod, p.VscTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeySlashMeterReplenishPeriod, p.SlashMeterReplenishPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeySlashMeterReplenishFraction, p.SlashMeterReplenishFraction, ccvtypes.ValidateStringFraction),
		paramtypes.NewParamSetPair(KeyMaxThrottledPackets, p.MaxThrottledPackets, ccvtypes.ValidatePositiveInt64),
		paramtypes.NewParamSetPair(KeyConsumerRewardDenomRegistrationFee, p.ConsumerRewardDenomRegistrationFee, ValidateCoin),
	}
}

func ValidateTemplateClient(i interface{}) error {
	cs, ok := i.(ibctmtypes.ClientState)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T, expected: %T", i, ibctmtypes.ClientState{})
	}

	// copy clientstate to prevent changing original pointer
	copiedClient := cs

	// populate zeroed fields with valid fields
	copiedClient.ChainId = "chainid"

	trustPeriod, err := ccvtypes.CalculateTrustPeriod(consumertypes.DefaultConsumerUnbondingPeriod, DefaultTrustingPeriodFraction)
	if err != nil {
		return fmt.Errorf("invalid TrustPeriodFraction: %T", err)
	}
	copiedClient.TrustingPeriod = trustPeriod

	copiedClient.UnbondingPeriod = consumertypes.DefaultConsumerUnbondingPeriod
	copiedClient.LatestHeight = clienttypes.NewHeight(0, 1)

	if err := copiedClient.Validate(); err != nil {
		return err
	}
	return nil
}

func ValidateCoin(i interface{}) error {
	v, ok := i.(sdk.Coin)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}

	if !v.IsValid() {
		return fmt.Errorf("invalid consumer reward denom registration fee: %s", v)
	}

	return nil
}
