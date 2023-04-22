package governance

import (
	"fmt"

	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/module"

	abci "github.com/cometbft/cometbft/abci/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	gov "github.com/cosmos/cosmos-sdk/x/gov"
	"github.com/cosmos/cosmos-sdk/x/gov/keeper"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
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
	isProposalWhitelisted func(govv1beta1.Content) bool
}

// NewAppModule creates a new AppModule object using the native x/governance module AppModule constructor.
func NewAppModule(cdc codec.Codec, keeper keeper.Keeper, ak govtypes.AccountKeeper, bk govtypes.BankKeeper, isProposalWhitelisted func(govv1beta1.Content) bool, ss govtypes.ParamSubspace) AppModule {
	govAppModule := gov.NewAppModule(cdc, &keeper, ak, bk, ss)
	return AppModule{
		AppModule:             govAppModule,
		keeper:                keeper,
		isProposalWhitelisted: isProposalWhitelisted,
	}
}

func (am AppModule) EndBlock(ctx sdk.Context, request abci.RequestEndBlock) []abci.ValidatorUpdate {
	am.keeper.IterateActiveProposalsQueue(ctx, ctx.BlockHeader().Time, func(proposal govv1.Proposal) bool {
		// if there are forbidden proposals in active proposals queue, refund deposit, delete votes for that proposal
		// and delete proposal from all storages
		deleteForbiddenProposal(ctx, am, proposal)
		return false
	})

	return am.AppModule.EndBlock(ctx, request)
}

func deleteForbiddenProposal(ctx sdk.Context, am AppModule, proposal govv1.Proposal) {
	message := proposal.GetMessages()[0]

	sdkMsg := &govv1.MsgExecLegacyContent{
		Content:   message,
		Authority: authtypes.NewModuleAddress(govtypes.ModuleName).String(),
	}

	content, err := govv1.LegacyContentFromMessage(sdkMsg)
	if err != nil {
		return
	}
	if am.isProposalWhitelisted(content) {
		return
	}
	// delete the votes related to the proposal calling Tally
	// Tally's return result won't be used in decision if the tokens will be burned or refunded (they are always refunded), but
	// this function needs to be called to delete the votes related to the given proposal, since the deleteVote function is
	// private and cannot be called directly from the overridden app module
	am.keeper.Tally(ctx, proposal)

	am.keeper.DeleteAndBurnDeposits(ctx, proposal.Id)
	am.keeper.RefundAndDeleteDeposits(ctx, proposal.Id)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			govtypes.EventTypeActiveProposal,
			sdk.NewAttribute(govtypes.AttributeKeyProposalID, fmt.Sprintf("%d", proposal.Id)),
			sdk.NewAttribute(govtypes.AttributeKeyProposalResult, AttributeValueProposalForbidden),
		),
	)

	logger := am.keeper.Logger(ctx)
	logger.Info(
		"proposal is not whitelisted; deleted",
		"proposal", proposal.Id,
		"title", proposal.GetTitle(),
		"total_deposit", proposal.TotalDeposit)
}
