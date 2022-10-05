package governance

import (
	"fmt"

	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/module"

	gov "github.com/cosmos/cosmos-sdk/x/gov"
	"github.com/cosmos/cosmos-sdk/x/gov/keeper"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

const (
	AttributeValueProposalForbidden = "proposal_forbidden"
)

var (
	_ module.AppModule           = AppModule{}
	_ module.AppModuleSimulation = AppModule{}
)

// AppModule embeds the Cosmos SDK's x/governance AppModule
type AppModule struct {
	// embed the Cosmos SDK's x/governance AppModule
	gov.AppModule

	keeper                keeper.Keeper
	isProposalWhitelisted func(govtypes.Content) bool
}

// NewAppModule creates a new AppModule object using the native x/governance module AppModule constructor.
func NewAppModule(cdc codec.Codec, keeper keeper.Keeper, ak govtypes.AccountKeeper, bk govtypes.BankKeeper, isProposalWhitelisted func(govtypes.Content) bool) AppModule {
	govAppModule := gov.NewAppModule(cdc, keeper, ak, bk)
	return AppModule{
		AppModule:             govAppModule,
		keeper:                keeper,
		isProposalWhitelisted: isProposalWhitelisted,
	}
}

func (am AppModule) EndBlock(ctx sdk.Context, request abci.RequestEndBlock) []abci.ValidatorUpdate {

	am.keeper.IterateActiveProposalsQueue(ctx, ctx.BlockHeader().Time, func(proposal govtypes.Proposal) bool {
		//if there are forbidden proposals in active proposals queue, refund deposit, delete votes for that proposal
		//and delete proposal from all storages
		deleteForbiddenProposal(ctx, am, proposal)
		return false
	})

	return am.AppModule.EndBlock(ctx, request)
}

func deleteForbiddenProposal(ctx sdk.Context, am AppModule, proposal govtypes.Proposal) {
	if am.isProposalWhitelisted(proposal.GetContent()) {
		return
	}

	//delete the votes related to the proposal calling Tally
	//Tally's return result won't be used in decision if the tokens will be burned or refunded (they are always refunded), but
	//this function needs to be called to delete the votes related to the given proposal, since the deleteVote function is
	// private and cannot be called directly from the overridden app module
	am.keeper.Tally(ctx, proposal)

	am.keeper.DeleteProposal(ctx, proposal.ProposalId)
	am.keeper.RefundDeposits(ctx, proposal.ProposalId)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			govtypes.EventTypeActiveProposal,
			sdk.NewAttribute(govtypes.AttributeKeyProposalID, fmt.Sprintf("%d", proposal.ProposalId)),
			sdk.NewAttribute(govtypes.AttributeKeyProposalResult, AttributeValueProposalForbidden),
		),
	)

	logger := am.keeper.Logger(ctx)
	logger.Info(
		"proposal is not whitelisted; deleted",
		"proposal", proposal.ProposalId,
		"title", proposal.GetTitle(),
		"total_deposit", proposal.TotalDeposit.String())
}
