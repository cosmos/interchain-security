package adminmodule

import (
	"fmt"
	"time"

	"github.com/cosmos/cosmos-sdk/telemetry"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	icahostkeeper "github.com/cosmos/ibc-go/v3/modules/apps/27-interchain-accounts/host/keeper"
	icatypes "github.com/cosmos/ibc-go/v3/modules/apps/27-interchain-accounts/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/keeper"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// EndBlocker called every block, process inflation, update validator set.
func EndBlocker(ctx sdk.Context, keeper keeper.Keeper, icahostkeeper icahostkeeper.Keeper, consumerkeeper consumerkeeper.Keeper) {
	defer telemetry.ModuleMeasureSince(types.ModuleName, time.Now(), telemetry.MetricKeyEndBlocker)

	logger := keeper.Logger(ctx)

	addGovernanceModuleAdmin(ctx, keeper, icahostkeeper, consumerkeeper)

	// fetch active proposals whose voting periods have ended (are passed the block time)
	keeper.IterateActiveProposalsQueue(ctx, ctx.BlockHeader().Time, func(proposal govtypes.Proposal) bool {
		var logMsg string

		handler := keeper.Router().GetRoute(proposal.ProposalRoute())
		cacheCtx, writeCache := ctx.CacheContext()

		// The proposal handler may execute state mutating logic depending
		// on the proposal content. If the handler fails, no state mutation
		// is written and the error message is logged.
		err := handler(cacheCtx, proposal.GetContent())
		if err == nil {
			logMsg = "passed"
			// write state to the underlying multi-store
			writeCache()
		} else {
			logMsg = fmt.Sprintf("passed, but failed on execution: %s", err)
		}

		proposal.Status = govtypes.StatusPassed

		keeper.SetProposal(ctx, proposal)
		keeper.RemoveFromActiveProposalQueue(ctx, proposal.ProposalId, proposal.SubmitTime.Add(2*time.Second)) // TODO hardcode

		keeper.AddToArchive(ctx, proposal)

		logger.Info(
			"proposal tallied",
			"proposal", proposal.ProposalId,
			"title", proposal.GetTitle(),
			"result", logMsg,
		)

		// TODO event?
		return false
	})
}

func addGovernanceModuleAdmin(ctx sdk.Context, keeper keeper.Keeper, icahostkeeper icahostkeeper.Keeper, consumerkeeper consumerkeeper.Keeper) {
	if keeper.IsProviderGovernanceAdminSet {
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

	// TODO Ethernal: should be read from consumerKeeper
	providerGovModAddress := "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn"

	portID, err := icatypes.NewControllerPortID(providerGovModAddress)
	if err != nil {
		return
	}

	govModICAAddress, found := icahostkeeper.GetInterchainAccountAddress(ctx, connHops[0], portID)
	if !found {
		return
	}

	keeper.SetAdmin(ctx, govModICAAddress)
	keeper.IsProviderGovernanceAdminSet = true
}
