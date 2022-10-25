package adminmodule

import (
	"fmt"
	"time"

	"github.com/cosmos/cosmos-sdk/telemetry"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	icatypes "github.com/cosmos/ibc-go/v3/modules/apps/27-interchain-accounts/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/keeper"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// EndBlocker called every block, process inflation, update validator set.
func EndBlocker(ctx sdk.Context, keeper keeper.Keeper, icahostkeeper types.ICAHostKeeper, consumerkeeper types.ConsumerKeeper) {
	defer telemetry.ModuleMeasureSince(types.ModuleName, time.Now(), telemetry.MetricKeyEndBlocker)

	logger := keeper.Logger(ctx)

	addGovernanceModuleAdmin(ctx, keeper, icahostkeeper, consumerkeeper)

	// fetch active proposals whose voting periods have ended (are passed the block time)
	keeper.IterateActiveProposalsQueue(ctx, ctx.BlockHeader().Time, func(proposal govtypes.Proposal) bool {
		var logMsg, tagValue string

		handler := keeper.Router().GetRoute(proposal.ProposalRoute())
		cacheCtx, writeCache := ctx.CacheContext()

		// The proposal handler may execute state mutating logic depending
		// on the proposal content. If the handler fails, no state mutation
		// is written and the error message is logged.
		err := handler(cacheCtx, proposal.GetContent())
		if err == nil {
			logMsg = "passed"
			proposal.Status = govtypes.StatusPassed
			tagValue = govtypes.AttributeValueProposalPassed

			// The cached context is created with a new EventManager. However, since
			// the proposal handler execution was successful, we want to track/keep
			// any events emitted, so we re-emit to "merge" the events into the
			// original Context's EventManager.
			ctx.EventManager().EmitEvents(cacheCtx.EventManager().Events())

			// write state to the underlying multi-store
			writeCache()
		} else {
			proposal.Status = govtypes.StatusFailed
			tagValue = govtypes.AttributeValueProposalFailed
			logMsg = fmt.Sprintf("proposal failed on execution: %s", err)
		}

		keeper.SetProposal(ctx, proposal)
		keeper.RemoveFromActiveProposalQueue(ctx, proposal.ProposalId, proposal.VotingEndTime)

		keeper.AddToArchive(ctx, proposal)

		logger.Info(
			"proposal tallied",
			"proposal", proposal.ProposalId,
			"title", proposal.GetTitle(),
			"result", logMsg,
		)

		ctx.EventManager().EmitEvent(
			sdk.NewEvent(
				types.EventTypeAdminProposal,
				sdk.NewAttribute(govtypes.AttributeKeyProposalID, fmt.Sprintf("%d", proposal.ProposalId)),
				sdk.NewAttribute(govtypes.AttributeKeyProposalResult, tagValue),
			),
		)
		return false
	})
}

func addGovernanceModuleAdmin(ctx sdk.Context, keeper keeper.Keeper, icahostkeeper types.ICAHostKeeper, consumerkeeper types.ConsumerKeeper) {
	if keeper.GetProviderICAAdmin(ctx) != "" {
		return
	}

	providerChannel, found := consumerkeeper.GetProviderChannel(ctx)
	if !found {
		return
	}

	connHops, err := consumerkeeper.GetConnectionHops(ctx, ccv.ConsumerPortID, providerChannel)
	if err != nil || len(connHops) == 0 {
		return
	}

	providerGovModAddress, found := consumerkeeper.GetProviderGovernanceAddress(ctx)
	if !found {
		return
	}

	portID, err := icatypes.NewControllerPortID(providerGovModAddress)
	if err != nil {
		return
	}

	govModICAAddress, found := icahostkeeper.GetInterchainAccountAddress(ctx, connHops[0], portID)
	if !found {
		return
	}

	keeper.SetAdmin(ctx, govModICAAddress)
	keeper.SetProviderICAAdmin(ctx, govModICAAddress)
}
