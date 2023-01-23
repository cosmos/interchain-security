package app

import (
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ibctransfertypes "github.com/cosmos/ibc-go/v4/modules/apps/transfer/types"
)

func IsProposalWhitelisted(content govtypes.Content) bool {

	switch c := content.(type) {
	case *proposal.ParameterChangeProposal:
		return isParamChangeWhitelisted(c.Changes)

	default:
		return false
	}

}

func isParamChangeWhitelisted(paramChanges []proposal.ParamChange) bool {
	for _, paramChange := range paramChanges {
		_, found := WhitelistedParams[paramChangeKey{Subspace: paramChange.Subspace, Key: paramChange.Key}]
		if !found {
			return false
		}
	}
	return true
}

type paramChangeKey struct {
	Subspace, Key string
}

var WhitelistedParams = map[paramChangeKey]struct{}{
	//bank
	{Subspace: banktypes.ModuleName, Key: "SendEnabled"}: {},
	//governance
	{Subspace: govtypes.ModuleName, Key: "depositparams"}: {}, //min_deposit, max_deposit_period
	{Subspace: govtypes.ModuleName, Key: "votingparams"}:  {}, //voting_period
	{Subspace: govtypes.ModuleName, Key: "tallyparams"}:   {}, //quorum,threshold,veto_threshold
	//staking
	{Subspace: stakingtypes.ModuleName, Key: "UnbondingTime"}:     {},
	{Subspace: stakingtypes.ModuleName, Key: "MaxValidators"}:     {},
	{Subspace: stakingtypes.ModuleName, Key: "MaxEntries"}:        {},
	{Subspace: stakingtypes.ModuleName, Key: "HistoricalEntries"}: {},
	{Subspace: stakingtypes.ModuleName, Key: "BondDenom"}:         {},
	//distribution
	{Subspace: distrtypes.ModuleName, Key: "communitytax"}:        {},
	{Subspace: distrtypes.ModuleName, Key: "baseproposerreward"}:  {},
	{Subspace: distrtypes.ModuleName, Key: "bonusproposerreward"}: {},
	{Subspace: distrtypes.ModuleName, Key: "withdrawaddrenabled"}: {},
	//mint
	{Subspace: minttypes.ModuleName, Key: "MintDenom"}:           {},
	{Subspace: minttypes.ModuleName, Key: "InflationRateChange"}: {},
	{Subspace: minttypes.ModuleName, Key: "InflationMax"}:        {},
	{Subspace: minttypes.ModuleName, Key: "InflationMin"}:        {},
	{Subspace: minttypes.ModuleName, Key: "GoalBonded"}:          {},
	{Subspace: minttypes.ModuleName, Key: "BlocksPerYear"}:       {},
	//ibc transfer
	{Subspace: ibctransfertypes.ModuleName, Key: "SendEnabled"}:    {},
	{Subspace: ibctransfertypes.ModuleName, Key: "ReceiveEnabled"}: {},
	//add interchain account params(HostEnabled, AllowedMessages) once the module is added to the consumer app
}
