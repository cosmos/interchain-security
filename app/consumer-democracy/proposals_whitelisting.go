package app

import (
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	"github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ibctransfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
)

func IsProposalWhitelisted(content v1beta1.Content) bool {
	switch c := content.(type) {
	case *proposal.ParameterChangeProposal:
		return isParamChangeWhitelisted(c.Changes)

	default:
		return false
	}
}

func isParamChangeWhitelisted(paramChanges []proposal.ParamChange) bool {
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

type paramChangeKey struct {
	MsgType, Key string
}

var WhitelistedParams = map[paramChangeKey]struct{}{
	// bank
	{MsgType: banktypes.TypeMsgUpdateParams, Key: "SendEnabled"}: {},
	// governance
	{MsgType: "cosmos.gov.v1.MsgUpdateParams", Key: "depositparams"}: {}, // min_deposit, max_deposit_period
	{MsgType: "cosmos.gov.v1.MsgUpdateParams", Key: "votingparams"}:  {}, // voting_period
	{MsgType: "cosmos.gov.v1.MsgUpdateParams", Key: "tallyparams"}:   {}, // quorum,threshold,veto_threshold
	// staking
	{MsgType: stakingtypes.TypeMsgUpdateParams, Key: "UnbondingTime"}:     {},
	{MsgType: stakingtypes.TypeMsgUpdateParams, Key: "MaxValidators"}:     {},
	{MsgType: stakingtypes.TypeMsgUpdateParams, Key: "MaxEntries"}:        {},
	{MsgType: stakingtypes.TypeMsgUpdateParams, Key: "HistoricalEntries"}: {},
	{MsgType: stakingtypes.TypeMsgUpdateParams, Key: "BondDenom"}:         {},
	// distribution
	{MsgType: distrtypes.TypeMsgUpdateParams, Key: "communitytax"}: {},
	// {Subspace: distrtypes.ModuleName, Key: "baseproposerreward"}:  {},   depricated key
	// {Subspace: distrtypes.ModuleName, Key: "bonusproposerreward"}: {},   depricated key
	{MsgType: distrtypes.TypeMsgUpdateParams, Key: "withdrawaddrenabled"}: {},
	// mint
	{MsgType: "cosmos.mint.v1beta1.MsgUpdateParams", Key: "MintDenom"}:           {},
	{MsgType: "cosmos.mint.v1beta1.MsgUpdateParams", Key: "InflationRateChange"}: {},
	{MsgType: "cosmos.mint.v1beta1.MsgUpdateParams", Key: "InflationMax"}:        {},
	{MsgType: "cosmos.mint.v1beta1.MsgUpdateParams", Key: "InflationMin"}:        {},
	{MsgType: "cosmos.mint.v1beta1.MsgUpdateParams", Key: "GoalBonded"}:          {},
	{MsgType: "cosmos.mint.v1beta1.MsgUpdateParams", Key: "BlocksPerYear"}:       {},
	// add interchain account params(HostEnabled, AllowedMessages) once the module is added to the consumer app
}
