package app

import (
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	"github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"
)

func IsProposalWhitelisted(content v1beta1.Content) bool {
	switch c := content.(type) {
	case *proposal.ParameterChangeProposal:
		return isLegacyParamChangeWhitelisted(c.Changes)
	default:
		return false
	}
}

func isLegacyParamChangeWhitelisted(paramChanges []proposal.ParamChange) bool {
	for _, paramChange := range paramChanges {
		_, found := LegacyWhitelistedParams[legacyParamChangeKey{Subspace: paramChange.Subspace, Key: paramChange.Key}]
		if !found {
			return false
		}
	}
	return true
}

type legacyParamChangeKey struct {
	Subspace, Key string
}

// these parameters don't exist in the consumer app -- keeping them as an
var LegacyWhitelistedParams = map[legacyParamChangeKey]struct{}{
	// add whitlisted legacy parameters here [cosmos-sdk <= 0.47]
	// commented parameters are just an example - most params have been moved to their respecitve modules
	// and they cannot be changed through legacy governance proposals
	{Subspace: banktypes.ModuleName, Key: "SendEnabled"}: {},
}

// add whitelisted module param update messages [cosmos-sdk >= 0.47]
var WhiteListModule = map[string]struct{}{
	"/cosmos.gov.v1.MsgUpdateParams":                {},
	"/cosmos.bank.v1beta1.MsgUpdateParams":          {},
	"/cosmos.staking.v1beta1.MsgUpdateParams":       {},
	"/cosmos.distribution.v1beta1.MsgUpdateParams":  {},
	"/cosmos.mint.v1beta1.MsgUpdateParams":          {},
	"/cosmos.gov.v1beta1.TextProposal":              {},
	"/ibc.applications.transfer.v1.MsgUpdateParams": {},
}

func IsModuleWhiteList(typeUrl string) bool {
	_, found := WhiteListModule[typeUrl]
	return found
}
