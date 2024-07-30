package keeper

import (
	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

func (k Keeper) HandleLegacyConsumerRewardDenomProposal(ctx sdk.Context, p *types.ChangeRewardDenomsProposal) error {
	for _, denomToAdd := range p.DenomsToAdd {
		// Log error and move on if one of the denoms is already registered
		if k.ConsumerRewardDenomExists(ctx, denomToAdd) {
			ctx.Logger().Error("denom %s already registered", denomToAdd)
			continue
		}
		k.SetConsumerRewardDenom(ctx, denomToAdd)
		ctx.EventManager().EmitEvent(sdk.NewEvent(
			types.EventTypeAddConsumerRewardDenom,
			sdk.NewAttribute(types.AttributeConsumerRewardDenom, denomToAdd),
		))
	}
	for _, denomToRemove := range p.DenomsToRemove {
		// Log error and move on if one of the denoms is not registered
		if !k.ConsumerRewardDenomExists(ctx, denomToRemove) {
			ctx.Logger().Error("denom %s not registered", denomToRemove)
			continue
		}
		k.DeleteConsumerRewardDenom(ctx, denomToRemove)
		ctx.EventManager().EmitEvent(sdk.NewEvent(
			types.EventTypeRemoveConsumerRewardDenom,
			sdk.NewAttribute(types.AttributeConsumerRewardDenom, denomToRemove),
		))
	}
	return nil
}

// HandleConsumerAdditionProposal will receive the consumer chain's client state from the proposal.
// If the client can be successfully created in a cached context, it stores the proposal as a pending proposal.
//
// Note: This method implements SpawnConsumerChainProposalHandler in spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcaprop1
// Spec tag: [CCV-PCF-HCAPROP.1]
func (k Keeper) HandleLegacyConsumerAdditionProposal(ctx sdk.Context, p *types.ConsumerAdditionProposal) error {
	// verify the consumer addition proposal execution
	// in cached context and discard the cached writes
	if _, _, err := k.CreateConsumerClientInCachedCtx(ctx, *p); err != nil {
		return err
	}

	k.SetPendingConsumerAdditionProp(ctx, p)

	k.Logger(ctx).Info("consumer addition proposal enqueued",
		"chainID", p.ChainId,
		"title", p.Title,
		"spawn time", p.SpawnTime.UTC(),
	)

	return nil
}

// HandleConsumerRemovalProposal stops a consumer chain and released the outstanding unbonding operations.
// If the consumer can be successfully stopped in a cached context, it stores the proposal as a pending proposal.
//
// This method implements StopConsumerChainProposalHandler from spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcrprop1
// Spec tag: [CCV-PCF-HCRPROP.1]
func (k Keeper) HandleLegacyConsumerRemovalProposal(ctx sdk.Context, p *types.ConsumerRemovalProposal) error {
	// verify the consumer removal proposal execution
	// in cached context and discard the cached writes
	if _, _, err := k.StopConsumerChainInCachedCtx(ctx, *p); err != nil {
		return err
	}

	k.SetPendingConsumerRemovalProp(ctx, p)

	k.Logger(ctx).Info("consumer removal proposal enqueued",
		"consumer id", p.ConsumerId,
		"title", p.Title,
		"stop time", p.StopTime.UTC(),
	)

	return nil
}

// HandleConsumerModificationProposal modifies a running consumer chain
func (k Keeper) HandleLegacyConsumerModificationProposal(ctx sdk.Context, p *types.ConsumerModificationProposal) error {
	if _, found := k.GetConsumerClientId(ctx, p.ConsumerId); !found {
		return errorsmod.Wrapf(types.ErrInvalidConsumerId, "chain with consumer id %s is not launched", p.ConsumerId)
	}

	k.SetTopN(ctx, p.ConsumerId, p.Top_N)
	k.SetValidatorsPowerCap(ctx, p.ConsumerId, p.ValidatorsPowerCap)
	k.SetValidatorSetCap(ctx, p.ConsumerId, p.ValidatorSetCap)
	k.SetMinStake(ctx, p.ConsumerId, p.MinStake)
	k.SetInactiveValidatorsAllowed(ctx, p.ConsumerId, p.AllowInactiveVals)

	k.DeleteAllowlist(ctx, p.ConsumerId)
	for _, address := range p.Allowlist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetAllowlist(ctx, p.ConsumerId, types.NewProviderConsAddress(consAddr))
	}

	k.DeleteDenylist(ctx, p.ConsumerId)
	for _, address := range p.Denylist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetDenylist(ctx, p.ConsumerId, types.NewProviderConsAddress(consAddr))
	}

	oldTopN, found := k.GetTopN(ctx, p.ConsumerId)
	if !found {
		oldTopN = 0
		k.Logger(ctx).Info("consumer chain top N not found, treating as 0", "chainID", p.ConsumerId)
	}

	// if the top N changes, we need to update the new minimum power in top N
	if p.Top_N != oldTopN {
		if p.Top_N > 0 {
			// if the chain receives a non-zero top N value, store the minimum power in the top N
			activeValidators, err := k.GetLastProviderConsensusActiveValidators(ctx)
			if err != nil {
				return err
			}
			minPower, err := k.ComputeMinPowerInTopN(ctx, activeValidators, p.Top_N)
			if err != nil {
				return err
			}
			k.SetMinimumPowerInTopN(ctx, p.ConsumerId, minPower)
		} else {
			// if the chain receives a zero top N value, we delete the min power
			k.DeleteMinimumPowerInTopN(ctx, p.ConsumerId)
		}
	}

	return nil
}
