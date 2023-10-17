package provider

import (
	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
)

// NewProviderProposalHandler defines the handler for consumer addition,
// consumer removal, and consumer reward denom proposals.
// Passed proposals are executed during EndBlock.
func NewProviderProposalHandler(k keeper.Keeper) govtypes.Handler {
	return func(ctx sdk.Context, content govtypes.Content) error {
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
