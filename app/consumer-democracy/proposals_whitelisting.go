package app

import (
	ibctransfertypes "github.com/cosmos/ibc-go/v8/modules/apps/transfer/types"

	"github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"
)

func IsProposalWhitelisted(content v1beta1.Content) bool {
	switch c := content.(type) {
	case *v1beta1.TextProposal:
		return true
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

var LegacyWhitelistedParams = map[legacyParamChangeKey]struct{}{
	// ibc transfer
	{Subspace: ibctransfertypes.ModuleName, Key: "SendEnabled"}:    {},
	{Subspace: ibctransfertypes.ModuleName, Key: "ReceiveEnabled"}: {},
	// add interchain account params(HostEnabled, AllowedMessages) once the module is added to the consumer app
}

var WhiteListModule = map[string]struct{}{
	"/cosmos.gov.v1.MsgUpdateParams":               {},
	"/cosmos.bank.v1beta1.MsgUpdateParams":         {},
	"/cosmos.staking.v1beta1.MsgUpdateParams":      {},
	"/cosmos.distribution.v1beta1.MsgUpdateParams": {},
	"/cosmos.mint.v1beta1.MsgUpdateParams":         {},
	"/cosmos.gov.v1beta1.TextProposal":             {},
}

func IsModuleWhiteList(typeUrl string) bool {
	_, found := WhiteListModule[typeUrl]
	return found
}
