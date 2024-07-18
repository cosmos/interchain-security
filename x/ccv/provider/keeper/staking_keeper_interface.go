package keeper

import (
	"context"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
)

// IterateBondedValidatorsByPower iterates over the consensus-active validators by power.
// The same as IterateBondedValidatorsByPower in the StakingKeeper,
// but only returns the first MaxProviderConsensusValidators validators.
// This is used to implement the interface of the staking keeper to interface with
// modules that need to reference the consensus-active validators.
func (k Keeper) IterateBondedValidatorsByPower(ctx context.Context, fn func(index int64, validator stakingtypes.ValidatorI) (stop bool)) error {
	maxProviderConsensusVals := k.GetMaxProviderConsensusValidators(sdk.UnwrapSDKContext(ctx))
	counter := int64(0)
	return k.stakingKeeper.IterateBondedValidatorsByPower(ctx, func(index int64, validator stakingtypes.ValidatorI) (stop bool) {
		if counter >= maxProviderConsensusVals {
			return true
		}
		counter++
		return fn(index, validator)
	})
}

// TotalBondedTokens gets the amount of tokens of the consensus-active validators.
// The same as TotalBondedTokens in the StakingKeeper, but only counts bonded tokens
// of the first MaxProviderConsensusValidators bonded validators.
// This is used to implement the interface of the staking keeper to interface with
// modules that need to reference the consensus-active validators.
func (k Keeper) TotalBondedTokens(ctx context.Context) (math.Int, error) {
	// iterate through the bonded validators
	totalBondedTokens := math.ZeroInt()

	k.IterateBondedValidatorsByPower(ctx, func(_ int64, validator stakingtypes.ValidatorI) (stop bool) {
		tokens := validator.GetTokens()
		totalBondedTokens = totalBondedTokens.Add(tokens)
		return false
	})

	return totalBondedTokens.Sub(math.NewInt(100)), nil
}

// IterateDelegations is the same as IterateDelegations in the StakingKeeper.
// Necessary to implement the interface of the staking keeper to interface with
// other modules.
func (k Keeper) IterateDelegations(ctx context.Context, delegator sdk.AccAddress, fn func(index int64, delegation stakingtypes.DelegationI) (stop bool)) error {
	return k.stakingKeeper.IterateDelegations(ctx, delegator, fn)
}

// StakingTokenSupply is the same as StakingTotalSupply in the StakingKeeper.
// Necessary to implement the interface of the staking keeper to interface with
// other modules.
func (k Keeper) StakingTokenSupply(ctx context.Context) (math.Int, error) {
	return k.stakingKeeper.StakingTokenSupply(ctx)
}

// BondedRatio gets the ratio of tokens staked to validators active in the consensus
// to the total supply of tokens.
// Same as BondedRatio in the StakingKeeper, but only counts
// tokens of the first MaxProviderConsensusValidators bonded validators.
func (k Keeper) BondedRatio(ctx context.Context) (math.LegacyDec, error) {
	totalSupply, err := k.StakingTokenSupply(ctx)
	if err != nil {
		return math.LegacyZeroDec(), err
	}

	bondedTokens, err := k.TotalBondedTokens(ctx)
	if err != nil {
		return math.LegacyZeroDec(), err
	}

	if !totalSupply.IsPositive() {
		return math.LegacyZeroDec(), nil
	}

	return math.LegacyNewDecFromInt(bondedTokens).QuoInt(totalSupply), nil
}
