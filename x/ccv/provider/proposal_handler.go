package provider

import (
	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// NewProviderProposalHandler defines the handler for consumer addition and removal proposals.
// Passed proposals are executed during EndBlock.
func NewProviderProposalHandler(k keeper.Keeper) govv1beta1.Handler {
	return func(ctx sdk.Context, content govv1beta1.Content) error {
		switch c := content.(type) {
		case *types.ConsumerAdditionProposal:
			return k.HandleConsumerAdditionProposal(ctx, c)
		case *types.ConsumerRemovalProposal:
			return k.HandleConsumerRemovalProposal(ctx, c)
		case *types.ChangeRewardDenomsProposal:
			return k.HandleConsumerRewardDenomProposal(ctx, c)
		default:
			return errorsmod.Wrapf(sdkerrors.ErrUnknownRequest, "unrecognized ccv proposal content type: %T", c)
		}
	}
}
