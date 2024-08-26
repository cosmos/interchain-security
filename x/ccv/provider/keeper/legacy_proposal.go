package keeper

import (
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
		"chain id", p.ChainId,
		"title", p.Title,
		"stop time", p.StopTime.UTC(),
	)

	return nil
}
