package app

import (
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ibctransfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
)

func IsProposalWhitelisted(content govv1beta1.Content) bool {
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
	// bank
	{Subspace: banktypes.ModuleName, Key: string(banktypes.KeySendEnabled)}: {},
	// governance
	{Subspace: govtypes.ModuleName, Key: string(govv1.ParamStoreKeyDepositParams)}: {}, // min_deposit, max_deposit_period
	{Subspace: govtypes.ModuleName, Key: string(govv1.ParamStoreKeyVotingParams)}:  {}, // voting_period
	{Subspace: govtypes.ModuleName, Key: string(govv1.ParamStoreKeyTallyParams)}:   {}, // quorum,threshold,veto_threshold
	// staking
	{Subspace: stakingtypes.ModuleName, Key: string(stakingtypes.KeyUnbondingTime)}:     {},
	{Subspace: stakingtypes.ModuleName, Key: string(stakingtypes.KeyMaxValidators)}:     {},
	{Subspace: stakingtypes.ModuleName, Key: string(stakingtypes.KeyMaxEntries)}:        {},
	{Subspace: stakingtypes.ModuleName, Key: string(stakingtypes.KeyHistoricalEntries)}: {},
	{Subspace: stakingtypes.ModuleName, Key: string(stakingtypes.KeyBondDenom)}:         {},
	// distribution
	{Subspace: distrtypes.ModuleName, Key: string(distrtypes.ParamStoreKeyCommunityTax)}:        {},
	{Subspace: distrtypes.ModuleName, Key: string(distrtypes.ParamStoreKeyWithdrawAddrEnabled)}: {},
	// mint
	{Subspace: minttypes.ModuleName, Key: string(minttypes.KeyMintDenom)}:           {},
	{Subspace: minttypes.ModuleName, Key: string(minttypes.KeyInflationRateChange)}: {},
	{Subspace: minttypes.ModuleName, Key: string(minttypes.KeyInflationMax)}:        {},
	{Subspace: minttypes.ModuleName, Key: string(minttypes.KeyInflationMin)}:        {},
	{Subspace: minttypes.ModuleName, Key: string(minttypes.KeyGoalBonded)}:          {},
	{Subspace: minttypes.ModuleName, Key: string(minttypes.KeyBlocksPerYear)}:       {},
	// ibc transfer
	{Subspace: ibctransfertypes.ModuleName, Key: string(ibctransfertypes.KeySendEnabled)}:    {},
	{Subspace: ibctransfertypes.ModuleName, Key: string(ibctransfertypes.KeyReceiveEnabled)}: {},
	// add interchain account params(HostEnabled, AllowedMessages) once the module is added to the consumer app
}
