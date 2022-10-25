package keeper

import (
	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

func (k Keeper) GetArchivedProposals(ctx sdk.Context) []*govtypes.Proposal {
	proposals := make([]*govtypes.Proposal, 0)

	store := prefix.NewStore(ctx.KVStore(k.storeKey), []byte(types.ArchiveKey))

	iterator := store.Iterator(nil, nil)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var proposal govtypes.Proposal

		k.MustUnmarshalProposal(iterator.Value(), &proposal)
		proposals = append(proposals, &proposal)
	}

	return proposals
}

func (k Keeper) AddToArchive(ctx sdk.Context, proposal govtypes.Proposal) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), []byte(types.ArchiveKey))

	bz := k.MustMarshalProposal(proposal)

	store.Set(types.ProposalKey(proposal.ProposalId), bz)
}
