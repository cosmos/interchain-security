package types

import (
	"fmt"
	"time"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
)

var (
	KeyTemplateClient = []byte("TemplateClient")
)

// ParamKeyTable type declaration for parameters
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new provider parameters with provided arguments
func NewParams(cs *ibctmtypes.ClientState) Params {
	return Params{
		TemplateClient: cs,
	}
}

// DefaultParams is the default params for the provider module
func DefaultParams() Params {
	// create default client state with chainID, trusting period, unbonding period, and inital height zeroed out.
	// these fields will be populated during proposal handler.
	return NewParams(
		ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*10, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"upgrade", "upgradedIBCState"}, true, true),
	)
}

// Validate all ccv-provider module parameters
func (p Params) Validate() error {
	if p.TemplateClient == nil {
		return fmt.Errorf("Template client is nil")
	}
	return validateTemplateClient(*p.TemplateClient)
}

// ParamSetPairs implements params.ParamSet
func (p *Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyTemplateClient, p.TemplateClient, validateTemplateClient),
	}
}

func validateTemplateClient(i interface{}) error {
	cs, ok := i.(ibctmtypes.ClientState)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}

	// copy clientstate to prevent changing original pointer
	var copiedClient ibctmtypes.ClientState
	copiedClient = cs

	// populate zeroed fields with valid fields
	copiedClient.ChainId = "chainid"
	copiedClient.TrustingPeriod = 3 * 7 * 24 * time.Hour
	copiedClient.UnbondingPeriod = 4 * 7 * 24 * time.Hour
	copiedClient.LatestHeight = clienttypes.NewHeight(0, 1)

	if err := copiedClient.Validate(); err != nil {
		return err
	}
	return nil
}
