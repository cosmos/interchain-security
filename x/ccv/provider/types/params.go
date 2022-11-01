package types

import (
	"fmt"
	"time"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

const (
	// DefaultMaxClockDrift defines how much new (untrusted) header's Time can drift into the future.
	// This default is only used in the default template client param.
	DefaultMaxClockDrift = 10 * time.Second

	// DefaultTrustingPeriodFraction is the default fraction used to compute TrustingPeriod
	// as UnbondingPeriod / TrustingPeriodFraction
	DefaultTrustingPeriodFraction = 2

	// DefaultInitTimeoutPeriod defines the init timeout period
	DefaultInitTimeoutPeriod = 7 * 24 * time.Hour

	// DefaultVscTimeoutPeriod defines the VSC timeout period
	DefaultVscTimeoutPeriod = 5 * 7 * 24 * time.Hour
)

// Reflection based keys for params subspace
var (
	KeyTemplateClient         = []byte("TemplateClient")
	KeyTrustingPeriodFraction = []byte("TrustingPeriodFraction")
	KeyInitTimeoutPeriod      = []byte("InitTimeoutPeriod")
	KeyVscTimeoutPeriod       = []byte("VscTimeoutPeriod")
)

// ParamKeyTable returns a key table with the necessary registered provider params
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new provider parameters with provided arguments
func NewParams(
	cs *ibctmtypes.ClientState,
	trustingPeriodFraction int64,
	ccvTimeoutPeriod time.Duration,
	initTimeoutPeriod time.Duration,
	vscTimeoutPeriod time.Duration,
) Params {
	return Params{
		TemplateClient:         cs,
		TrustingPeriodFraction: trustingPeriodFraction,
		CcvTimeoutPeriod:       ccvTimeoutPeriod,
		InitTimeoutPeriod:      initTimeoutPeriod,
		VscTimeoutPeriod:       vscTimeoutPeriod,
	}
}

// DefaultParams is the default params for the provider module
func DefaultParams() Params {
	// create default client state with chainID, trusting period, unbonding period, and inital height zeroed out.
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
			true,
			true,
		),
		DefaultTrustingPeriodFraction,
		ccvtypes.DefaultCCVTimeoutPeriod,
		DefaultInitTimeoutPeriod,
		DefaultVscTimeoutPeriod,
	)
}

// Validate all ccv-provider module parameters
func (p Params) Validate() error {
	if p.TemplateClient == nil {
		return fmt.Errorf("template client is nil")
	}
	if err := validateTemplateClient(*p.TemplateClient); err != nil {
		return err
	}
	if err := ccvtypes.ValidatePositiveInt64(p.TrustingPeriodFraction); err != nil {
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
	return nil
}

// ParamSetPairs implements params.ParamSet
func (p *Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyTemplateClient, p.TemplateClient, validateTemplateClient),
		paramtypes.NewParamSetPair(KeyTrustingPeriodFraction, p.TrustingPeriodFraction, ccvtypes.ValidatePositiveInt64),
		paramtypes.NewParamSetPair(ccvtypes.KeyCCVTimeoutPeriod, p.CcvTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeyInitTimeoutPeriod, p.InitTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeyVscTimeoutPeriod, p.VscTimeoutPeriod, ccvtypes.ValidateDuration),
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
	copiedClient.TrustingPeriod = consumertypes.DefaultConsumerUnbondingPeriod / DefaultTrustingPeriodFraction
	copiedClient.UnbondingPeriod = consumertypes.DefaultConsumerUnbondingPeriod
	copiedClient.LatestHeight = clienttypes.NewHeight(0, 1)

	if err := copiedClient.Validate(); err != nil {
		return err
	}
	return nil
}
