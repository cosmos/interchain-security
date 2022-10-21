package types

import (
	"fmt"
	"time"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

const (
	// DefaultTrustingPeriod is duration of the period since
	// the LastestTimestamp during which the submitted headers are valid for upgrade
	DefaultTrustingPeriod = 3 * 7 * 24 * time.Hour

	// DefaultUnbondingPeriod of the staking unbonding period
	DefaultUnbondingPeriod = 4 * 7 * 24 * time.Hour

	// DefaultMaxClockDrift defines how much new (untrusted) header's Time can drift into the future.
	DefaultMaxClockDrift = 10 * time.Second

	// DefaultTrustingPeriodFraction is the default fraction used to compute TrustingPeriod
	// as UnbondingPeriod / TrustingPeriodFraction
	DefaultTrustingPeriodFraction = 2
)

// Reflection based keys for params subspace
var (
	KeyTemplateClient         = []byte("TemplateClient")
	KeyTrustingPeriodFraction = []byte("TrustingPeriodFraction")
)

// ParamKeyTable returns a key table with the necessary registered provider params
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new provider parameters with provided arguments
func NewParams(cs *ibctmtypes.ClientState, ccvTimeoutPeriod time.Duration,
	trustingPeriodFraction int64) Params {
	return Params{
		TemplateClient:         cs,
		CcvTimeoutPeriod:       ccvTimeoutPeriod,
		TrustingPeriodFraction: trustingPeriodFraction,
	}
}

// DefaultParams is the default params for the provider module
func DefaultParams() Params {
	// create default client state with chainID, trusting period, unbonding period, and inital height zeroed out.
	// these fields will be populated during proposal handler.
	return NewParams(
		ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			DefaultMaxClockDrift, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"upgrade", "upgradedIBCState"}, true, true),
		ccvtypes.DefaultCCVTimeoutPeriod,
		DefaultTrustingPeriodFraction,
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
	if err := ccvtypes.ValidateDuration(p.CcvTimeoutPeriod); err != nil {
		return err
	}
	if err := ccvtypes.ValidatePositiveInt64(p.TrustingPeriodFraction); err != nil {
		return err
	}
	return nil
}

// ParamSetPairs implements params.ParamSet
func (p *Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyTemplateClient, p.TemplateClient, validateTemplateClient),
		paramtypes.NewParamSetPair(ccvtypes.KeyCCVTimeoutPeriod, p.CcvTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeyTrustingPeriodFraction, p.TrustingPeriodFraction, ccvtypes.ValidatePositiveInt64),
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
	copiedClient.TrustingPeriod = DefaultTrustingPeriod
	copiedClient.UnbondingPeriod = DefaultUnbondingPeriod
	copiedClient.LatestHeight = clienttypes.NewHeight(0, 1)

	if err := copiedClient.Validate(); err != nil {
		return err
	}
	return nil
}
