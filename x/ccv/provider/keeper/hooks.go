package keeper

import (
	"fmt"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// Wrapper struct
type Hooks struct {
	k *Keeper
}

var _ stakingtypes.StakingHooks = Hooks{}

// Returns new provider hooks
func (k *Keeper) Hooks() Hooks {
	return Hooks{k}
}

// This stores a record of each unbonding op from staking, allowing us to track which consumer chains have unbonded
func (h Hooks) AfterUnbondingInitiated(ctx sdk.Context, ID uint64) error {
	var consumerChainIDS []string

	h.k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID, clientID string) (stop bool) {
		consumerChainIDS = append(consumerChainIDS, chainID)
		return false // do not stop the iteration
	})
	if len(consumerChainIDS) == 0 {
		// Do not put the unbonding op on hold if there are no consumer chains
		return nil
	}
	valsetUpdateID := h.k.GetValidatorSetUpdateId(ctx)
	unbondingOp := ccv.UnbondingOp{
		Id:                      ID,
		UnbondingConsumerChains: consumerChainIDS,
	}

	// Add to indexes
	for _, consumerChainID := range consumerChainIDS {
		index, _ := h.k.GetUnbondingOpIndex(ctx, consumerChainID, valsetUpdateID)
		index = append(index, ID)
		h.k.SetUnbondingOpIndex(ctx, consumerChainID, valsetUpdateID, index)
	}

	h.k.SetUnbondingOp(ctx, unbondingOp)

	// Call back into staking to tell it to stop this op from unbonding when the unbonding period is complete
	if err := h.k.stakingKeeper.PutUnbondingOnHold(ctx, ID); err != nil {
		// If there was an error putting the unbonding on hold, panic to end execution for
		// the current tx and prevent committal of this invalid state.
		panic(fmt.Errorf("unbonding could not be put on hold: %w", err))
	}
	return nil
}

// Define unimplemented methods to satisfy the StakingHooks contract
func (h Hooks) AfterValidatorCreated(ctx sdk.Context, valAddr sdk.ValAddress) {
}
func (h Hooks) AfterValidatorRemoved(ctx sdk.Context, _ sdk.ConsAddress, valAddr sdk.ValAddress) {
}
func (h Hooks) BeforeDelegationCreated(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) {
}
func (h Hooks) BeforeDelegationSharesModified(_ sdk.Context, _ sdk.AccAddress, _ sdk.ValAddress) {
}
func (h Hooks) AfterDelegationModified(_ sdk.Context, _ sdk.AccAddress, _ sdk.ValAddress) {
}
func (h Hooks) BeforeValidatorSlashed(_ sdk.Context, _ sdk.ValAddress, _ sdk.Dec) {
}
func (h Hooks) BeforeValidatorModified(_ sdk.Context, _ sdk.ValAddress) {
}
func (h Hooks) AfterValidatorBonded(_ sdk.Context, _ sdk.ConsAddress, _ sdk.ValAddress) {
}
func (h Hooks) AfterValidatorBeginUnbonding(_ sdk.Context, _ sdk.ConsAddress, _ sdk.ValAddress) {
}
func (h Hooks) BeforeDelegationRemoved(_ sdk.Context, _ sdk.AccAddress, _ sdk.ValAddress) {
}
