package keeper

import (
	"fmt"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
)

// SetLastProviderConsensusValidator sets the given validator to be stored
// as part of the last provider consensus validator set
func (k Keeper) SetLastProviderConsensusValidator(
	ctx sdk.Context,
	validator types.ConsensusValidator,
) error {
	return k.setValidator(ctx, types.LastProviderConsensusValsPrefix(), validator)
}

// SetLastProviderConsensusValSet resets the stored last validator set sent to the consensus engine on the provider
// to the provided `nextValidators`.
func (k Keeper) SetLastProviderConsensusValSet(ctx sdk.Context, nextValidators []types.ConsensusValidator) error {
	return k.setValSet(ctx, types.LastProviderConsensusValsPrefix(), nextValidators)
}

// DeleteLastProviderConsensusValidator removes the validator with `providerConsAddr` address
// from the stored last provider consensus validator set
func (k Keeper) DeleteLastProviderConsensusValidator(
	ctx sdk.Context,
	providerConsAddr types.ProviderConsAddress,
) {
	k.deleteValidator(ctx, types.LastProviderConsensusValsPrefix(), providerConsAddr)
}

// DeleteLastProviderConsensusValSet deletes all the stored validators from the
// last provider consensus validator set
func (k Keeper) DeleteLastProviderConsensusValSet(
	ctx sdk.Context,
) {
	k.deleteValSet(ctx, types.LastProviderConsensusValsPrefix())
}

// GetLastProviderConsensusValSet returns the last stored
// validator set sent to the consensus engine on the provider
func (k Keeper) GetLastProviderConsensusValSet(
	ctx sdk.Context,
) ([]types.ConsensusValidator, error) {
	return k.getValSet(ctx, types.LastProviderConsensusValsPrefix())
}

// GetLastTotalProviderConsensusPower returns the total power of the last stored
// validator set sent to the consensus engine on the provider
func (k Keeper) GetLastTotalProviderConsensusPower(
	ctx sdk.Context,
) (math.Int, error) {
	return k.getTotalPower(ctx, types.LastProviderConsensusValsPrefix())
}

// CreateProviderConsensusValidator creates a new ConsensusValidator from the given staking validator
func (k Keeper) CreateProviderConsensusValidator(ctx sdk.Context, val stakingtypes.Validator) (types.ConsensusValidator, error) {
	consAddr, err := val.GetConsAddr()
	if err != nil {
		return types.ConsensusValidator{}, fmt.Errorf("getting consensus address: %w", err)
	}
	pubKey, err := val.TmConsPublicKey()
	if err != nil {
		return types.ConsensusValidator{}, fmt.Errorf("getting consensus public key: %w", err)
	}
	valAddr, err := sdk.ValAddressFromBech32(val.GetOperator())
	if err != nil {
		return types.ConsensusValidator{}, fmt.Errorf("getting validator address: %w", err)
	}

	power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
	if err != nil {
		return types.ConsensusValidator{}, fmt.Errorf("getting validator power: %w", err)
	}

	return types.ConsensusValidator{
		ProviderConsAddr: consAddr,
		PublicKey:        &pubKey,
		Power:            power,
	}, nil
}
