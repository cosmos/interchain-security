package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// Wrapper for the new proposal message MsgChangeRewardDenoms
// Will replace legacy handler HandleLegacyConsumerRewardDenomProposal
func (k Keeper) HandleConsumerRewardDenomProposal(ctx sdk.Context, proposal *types.MsgChangeRewardDenoms) error {
	p := types.ChangeRewardDenomsProposal{
		DenomsToAdd:    proposal.DenomsToAdd,
		DenomsToRemove: proposal.DenomsToRemove,
	}

	return k.HandleLegacyConsumerRewardDenomProposal(ctx, &p)
}
