package keeper

import (
	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// SetLastProviderConsensusValidator sets the given validator to be stored
// as part of the last provider consensus validator set
func (k Keeper) SetLastProviderConsensusValidator(
	ctx sdk.Context,
	validator types.ConsumerValidator,
) {
	k.setValidator(ctx, []byte{types.LastProviderConsensusValsPrefix}, validator)
}

// SetLastProviderConsensusValSet resets the stored last validator set sent to the consensus engine on the provider
// to the provided nextValidators.
func (k Keeper) SetLastProviderConsensusValSet(ctx sdk.Context, nextValidators []types.ConsumerValidator) {
	k.setValSet(ctx, []byte{types.LastProviderConsensusValsPrefix}, nextValidators)
}

// DeleteLastProviderConsensusValidator removes the validator with `providerConsAddr` address
// from the stored last provider consensus validator set
func (k Keeper) DeleteLastProviderConsensusValidator(
	ctx sdk.Context,
	providerConsAddr types.ProviderConsAddress,
) {
	k.deleteValidator(ctx, []byte{types.LastProviderConsensusValsPrefix}, providerConsAddr)
}

// DeleteLastProviderConsensusValSet deletes all the stored validators from the
// last provider consensus validator set
func (k Keeper) DeleteLastProviderConsensusValSet(
	ctx sdk.Context,
) {
	k.deleteValSet(ctx, []byte{types.LastProviderConsensusValsPrefix})
}

// GetLastProviderConsensusValSet returns the last stored
// validator set sent to the consensus engine on the provider
func (k Keeper) GetLastProviderConsensusValSet(
	ctx sdk.Context,
) []types.ConsumerValidator {
	return k.getValSet(ctx, []byte{types.LastProviderConsensusValsPrefix})
}

// GetLastTotalProviderConsensusPower returns the total power of the last stored
// validator set sent to the consensus engine on the provider
func (k Keeper) GetLastTotalProviderConsensusPower(
	ctx sdk.Context,
) math.Int {
	return k.getTotalPower(ctx, []byte{types.LastProviderConsensusValsPrefix})
}
