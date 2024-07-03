package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	types "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// RegisterInvariants registers all staking invariants
func RegisterInvariants(ir sdk.InvariantRegistry, k *Keeper) {
	ir.RegisterRoute(types.ModuleName, "max-provider-validators",
		MaxProviderConsensusValidatorsInvariant(k))
}

// MaxProviderConsensusValidatorsInvariant checks that the number of provider consensus validators
// is less than or equal to the maximum number of provider consensus validators
func MaxProviderConsensusValidatorsInvariant(k *Keeper) sdk.Invariant {
	return func(ctx sdk.Context) (string, bool) {
		params := k.GetParams(ctx)
		maxProviderConsensusValidators := params.MaxProviderConsensusValidators

		consensusValidators := k.GetLastProviderConsensusValSet(ctx)
		if int64(len(consensusValidators)) > maxProviderConsensusValidators {
			return sdk.FormatInvariant(types.ModuleName, "max-provider-validators",
				fmt.Sprintf("number of provider consensus validators: %d, exceeds max: %d",
					len(consensusValidators), maxProviderConsensusValidators)), true
		}

		return "", false
	}
}
