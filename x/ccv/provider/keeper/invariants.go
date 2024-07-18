package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	types "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// RegisterInvariants registers all staking invariants
func RegisterInvariants(ir sdk.InvariantRegistry, k *Keeper) {
	ir.RegisterRoute(types.ModuleName, "max-provider-validators",
		MaxProviderConsensusValidatorsInvariant(k))

	ir.RegisterRoute(types.ModuleName, "staking-keeper-equivalence",
		StakingKeeperEquivalenceInvariant(*k))
}

// MaxProviderConsensusValidatorsInvariant checks that the number of provider consensus validators
// is less than or equal to the maximum number of provider consensus validators
func MaxProviderConsensusValidatorsInvariant(k *Keeper) sdk.Invariant {
	return func(ctx sdk.Context) (string, bool) {
		params := k.GetParams(ctx)
		maxProviderConsensusValidators := params.MaxProviderConsensusValidators

		consensusValidators, err := k.GetLastProviderConsensusValSet(ctx)
		if err != nil {
			panic(fmt.Errorf("failed to get last provider consensus validator set: %w", err))
		}
		if int64(len(consensusValidators)) > maxProviderConsensusValidators {
			return sdk.FormatInvariant(types.ModuleName, "max-provider-validators",
				fmt.Sprintf("number of provider consensus validators: %d, exceeds max: %d",
					len(consensusValidators), maxProviderConsensusValidators)), true
		}

		return "", false
	}
}

// StakingKeeperEquivalenceInvariant checks that *if* MaxProviderConsensusValidators == MaxValidators, then
// the staking keeper and the provider keeper
// return the same values for their common interface,
// i.e. the functions from staking_keeper_interface.go
func StakingKeeperEquivalenceInvariant(k Keeper) sdk.Invariant {
	return func(ctx sdk.Context) (string, bool) {
		maxProviderConsensusValidators := k.GetParams(ctx).MaxProviderConsensusValidators
		if maxProviderConsensusValidators == 0 {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("maxProviderConsensusVals is 0: %v", maxProviderConsensusValidators)), true
		}
		stakingKeeper := k.stakingKeeper

		maxValidators, err := stakingKeeper.MaxValidators(ctx)
		if err != nil {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("error getting max validators from staking keeper: %v", err)), true
		}

		if maxValidators != uint32(maxProviderConsensusValidators) {
			// the invariant should only check something if these two numbers are equal,
			// so skip in this case
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("maxValidators: %v, maxProviderVals: %v", maxValidators, maxProviderConsensusValidators)), true
		}

		// check that the staking keeper and the provider keeper return the same values
		// for the common interface functions

		// Check IterateBondedValidatorsByPower
		providerBondedValidators := make([]stakingtypes.Validator, 0)
		err = k.IterateBondedValidatorsByPower(ctx, func(index int64, validator stakingtypes.ValidatorI) (stop bool) {
			providerBondedValidators = append(providerBondedValidators, validator.(stakingtypes.Validator))
			return false
		})
		if err != nil {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("error getting provider bonded validators: %v", err)), true
		}

		stakingBondedValidators := make([]stakingtypes.Validator, 0)
		err = stakingKeeper.IterateBondedValidatorsByPower(ctx, func(index int64, validator stakingtypes.ValidatorI) (stop bool) {
			stakingBondedValidators = append(stakingBondedValidators, validator.(stakingtypes.Validator))
			return false
		})
		if err != nil {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("error getting staking bonded validators: %v", err)), true
		}

		if len(providerBondedValidators) != len(stakingBondedValidators) {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("provider bonded validators: %v, staking bonded validators: %v",
					providerBondedValidators, stakingBondedValidators)), true
		}

		for i, providerVal := range providerBondedValidators {
			stakingVal := stakingBondedValidators[i]

			if providerVal.Equal(&stakingVal) {
				return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
					fmt.Sprintf("provider validator: %v, staking validator: %v",
						providerVal.GetOperator(), stakingVal.GetOperator())), true
			}
		}

		// Check TotalBondedTokens
		providerTotalBondedTokens, err := k.TotalBondedTokens(ctx)
		if err != nil {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("error getting provider total bonded tokens: %v", err)), true
		}

		stakingTotalBondedTokens, err := stakingKeeper.TotalBondedTokens(ctx)
		if err != nil {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("error getting staking total bonded tokens: %v", err)), true
		}

		if !providerTotalBondedTokens.Equal(stakingTotalBondedTokens) {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("provider total bonded tokens: %v, staking total bonded tokens: %v",
					providerTotalBondedTokens, stakingTotalBondedTokens)), true
		}

		// Check BondedRatio
		providerBondedRatio, err := k.BondedRatio(ctx)
		if err != nil {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("error getting provider bonded ratio: %v", err)), true
		}

		stakingBondedRatio, err := stakingKeeper.BondedRatio(ctx)
		if err != nil {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("error getting staking bonded ratio: %v", err)), true
		}

		if !providerBondedRatio.Equal(stakingBondedRatio) {
			return sdk.FormatInvariant(types.ModuleName, "staking-keeper-equivalence",
				fmt.Sprintf("provider bonded ratio: %v, staking bonded ratio: %v",
					providerBondedRatio, stakingBondedRatio)), true
		}

		return "", false
	}
}
