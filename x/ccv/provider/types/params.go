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
)

// Reflection based keys for params subspace
var (
	KeyTemplateClient = []byte("TemplateClient")
)

// ParamKeyTable returns a key table with the necessary registered provider params
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new provider parameters with provided arguments
func NewParams(cs *ibctmtypes.ClientState, ccvTimeoutPeriod time.Duration) Params {
	return Params{
		TemplateClient:   cs,
		CcvTimeoutPeriod: ccvTimeoutPeriod,
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
	)
}

// Validate all ccv-provider module parameters
func (p Params) Validate() error {
	if p.TemplateClient == nil {
		return fmt.Errorf("template client is nil")
	}
	if ccvtypes.ValidateDuration(p.CcvTimeoutPeriod) != nil {
		return fmt.Errorf("ccv timeout period is invalid")
	}
	return validateTemplateClient(*p.TemplateClient)
}

// ParamSetPairs implements params.ParamSet
func (p *Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyTemplateClient, p.TemplateClient, validateTemplateClient),
		paramtypes.NewParamSetPair(ccvtypes.KeyCCVTimeoutPeriod, p.CcvTimeoutPeriod, ccvtypes.ValidateDuration),
	}
}

func validateTemplateClient(i interface{}) error {
	cs, ok := i.(ibctmtypes.ClientState)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
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
