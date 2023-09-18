package keeper

import (
	"context"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
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
func (h Hooks) AfterUnbondingInitiated(ctx context.Context, id uint64) error {
	var consumerChainIDS []string

	// TODO: @MSalopek -> use context.Context in all ccv methods
	sdkCtx := sdk.UnwrapSDKContext(ctx)

	for _, chain := range h.k.GetAllConsumerChains(sdkCtx) {
		consumerChainIDS = append(consumerChainIDS, chain.ChainId)
	}

	if len(consumerChainIDS) == 0 {
		// Do not put the unbonding op on hold if there are no consumer chains
		return nil
	}
	// Call back into staking to tell it to stop this op from unbonding when the unbonding period is complete
	if err := h.k.stakingKeeper.PutUnbondingOnHold(ctx, id); err != nil {
		// Note: that in the case of a validator unbonding, AfterUnbondingInitiated is called
		// from staking.EndBlock.

		// In this case PutUnbondingOnHold fails if either the unbonding operation was
		// not found or the UnbondingOnHoldRefCount is negative.

		// This change should be updated for SDK v0.48 because it will include changes in handling
		// check: https://github.com/cosmos/cosmos-sdk/pull/16043
		h.k.Logger(ctx).Error("unbonding could not be put on hold: %w", err)
		return nil
	}

	valsetUpdateID := h.k.GetValidatorSetUpdateId(sdkCtx)
	unbondingOp := providertypes.UnbondingOp{
		Id:                      id,
		UnbondingConsumerChains: consumerChainIDS,
	}

	// Add to indexes
	for _, consumerChainID := range consumerChainIDS {
		index, _ := h.k.GetUnbondingOpIndex(sdkCtx, consumerChainID, valsetUpdateID)
		index = append(index, id)
		h.k.SetUnbondingOpIndex(sdkCtx, consumerChainID, valsetUpdateID, index)
	}

	h.k.SetUnbondingOp(sdkCtx, unbondingOp)

	// NOTE: This is a temporary fix for v0.47 -> we should not panic in this edge case
	// since the AfterUnbondInitiatedHook can be called with a non-existing UnbondingEntry.id
	// check: https://github.com/cosmos/cosmos-sdk/pull/16043
	//
	// Call back into staking to tell it to stop this op from unbonding when the unbonding period is complete
	// if err := h.k.stakingKeeper.PutUnbondingOnHold(ctx, id); err != nil {
	// 	// If there was an error putting the unbonding on hold, panic to end execution for
	// 	// the current tx and prevent committal of this invalid state.
	// 	//
	// 	// Note: that in the case of a validator unbonding, AfterUnbondingInitiated is called
	// 	// from staking.EndBlock, thus the following panic would halt the chain.
	// 	// In this case PutUnbondingOnHold fails if either the unbonding operation was
	// 	// not found or the UnbondingOnHoldRefCount is negative. In either cases,
	// 	// the state of the x/staking module of cosmos-sdk is invalid.
	// 	panic(fmt.Errorf("unbonding could not be put on hold: %w", err))
	// }
	return nil
}

// ValidatorConsensusKeyInUse is called when a new validator is created
// in the x/staking module of cosmos-sdk. In case it panics, the TX aborts
// and thus, the validator is not created. See AfterValidatorCreated hook.
func ValidatorConsensusKeyInUse(k *Keeper, ctx sdk.Context, valAddr sdk.ValAddress) bool {
	// Get the validator being added in the staking module.
	val, found := k.stakingKeeper.GetValidator(ctx, valAddr)
	if !found {
		// Abort TX, do NOT allow validator to be created
		panic("did not find newly created validator in staking module")
	}

	// Get the consensus address of the validator being added
	consensusAddr, err := val.GetConsAddr()
	if err != nil {
		// Abort TX, do NOT allow validator to be created
		panic("could not get validator cons addr ")
	}

	inUse := false

	for _, validatorConsumerAddrs := range k.GetAllValidatorsByConsumerAddr(ctx, nil) {
		if sdk.ConsAddress(validatorConsumerAddrs.ConsumerAddr).Equals(sdk.ConsAddress(consensusAddr)) {
			inUse = true
			break
		}
	}

	return inUse
}

func (h Hooks) AfterValidatorCreated(ctx context.Context, valAddr sdk.ValAddress) error {
	// TODO: @MSalopek -> use context.Context in all ccv methods
	sdkCtx := sdk.UnwrapSDKContext(ctx)

	if ValidatorConsensusKeyInUse(h.k, sdkCtx, valAddr) {
		// Abort TX, do NOT allow validator to be created
		panic("cannot create a validator with a consensus key that is already in use or was recently in use as an assigned consumer chain key")
	}
	return nil
}

func (h Hooks) AfterValidatorRemoved(ctx context.Context, valConsAddr sdk.ConsAddress, valAddr sdk.ValAddress) error {
	// TODO: @MSalopek -> use context.Context in all ccv methods
	sdkCtx := sdk.UnwrapSDKContext(ctx)

	for _, validatorConsumerPubKey := range h.k.GetAllValidatorConsumerPubKeys(sdkCtx, nil) {
		if sdk.ConsAddress(validatorConsumerPubKey.ProviderAddr).Equals(valConsAddr) {
			consumerAddrTmp, err := ccvtypes.TMCryptoPublicKeyToConsAddr(*validatorConsumerPubKey.ConsumerKey)
			if err != nil {
				// An error here would indicate something is very wrong
				panic("cannot get address of consumer key")
			}
			consumerAddr := providertypes.NewConsumerConsAddress(consumerAddrTmp)
			h.k.DeleteValidatorByConsumerAddr(sdkCtx, validatorConsumerPubKey.ChainId, consumerAddr)
			providerAddr := providertypes.NewProviderConsAddress(validatorConsumerPubKey.ProviderAddr)
			h.k.DeleteValidatorConsumerPubKey(sdkCtx, validatorConsumerPubKey.ChainId, providerAddr)
		}
	}

	return nil
}

func (h Hooks) BeforeDelegationCreated(ctx context.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) error {
	return nil
}

func (h Hooks) BeforeDelegationSharesModified(_ context.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) AfterDelegationModified(_ context.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) BeforeValidatorSlashed(_ context.Context, _ sdk.ValAddress, _ math.LegacyDec) error {
	return nil
}

func (h Hooks) BeforeValidatorModified(_ context.Context, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) AfterValidatorBonded(_ context.Context, _ sdk.ConsAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) AfterValidatorBeginUnbonding(_ context.Context, _ sdk.ConsAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) BeforeDelegationRemoved(_ context.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}
