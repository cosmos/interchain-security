package governance

import (
	"fmt"

	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/module"
	gov "github.com/cosmos/cosmos-sdk/x/gov"
	govkeeper "github.com/cosmos/cosmos-sdk/x/gov/keeper"
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

	keeper                      govkeeper.Keeper
	isLegacyProposalWhitelisted func(govv1beta1.Content) bool
	isModuleWhiteList           func(string) bool
}

type ParamChangeKey struct {
	MsgType, Key string
}

// NewAppModule creates a new AppModule object using the native x/governance module AppModule constructor.
func NewAppModule(cdc codec.Codec,
	keeper govkeeper.Keeper,
	ak govtypes.AccountKeeper,
	bk govtypes.BankKeeper,
	isProposalWhitelisted func(govv1beta1.Content) bool,
	ss govtypes.ParamSubspace,
	isModuleWhiteList func(string) bool,
) AppModule {
	govAppModule := gov.NewAppModule(cdc, &keeper, ak, bk, ss)
	return AppModule{
		AppModule:                   govAppModule,
		keeper:                      keeper,
		isLegacyProposalWhitelisted: isProposalWhitelisted,
		isModuleWhiteList:           isModuleWhiteList,
	}
}

// @MSalopek this returns an error and not validators
func (am AppModule) EndBlocker(ctx sdk.Context) error {
	// am.keeper.IterateActiveProposalsQueue(ctx, ctx.BlockHeader().Time, func(proposal govv1.Proposal) bool {
	// 	// if there are forbidden proposals in active proposals queue, refund deposit, delete votes for that proposal
	// 	// and delete proposal from all storages
	// 	deleteForbiddenProposal(ctx, am, proposal)
	// 	return false
	// })

	// TODO: @MSalopek use new approach for handling props
	// https://github.com/cosmos/cosmos-sdk/blob/87ba5a6a1368726cf0d19e2ffe1c835c4c5c5753/x/gov/abci.go#L77
	// err = keeper.ActiveProposalsQueue.Walk(ctx, rng, func(key collections.Pair[time.Time, uint64], _ uint64) (bool, error) {
	// 	proposal, err := keeper.Proposals.Get(ctx, key.K2())
	// 	if err != nil {
	// 		return false, err
	// 	}

	// 	var tagValue, logMsg string

	// 	passes, burnDeposits, tallyResults, err := keeper.Tally(ctx, proposal)
	// 	if err != nil {
	// 		return false, err
	// 	}

	// 	// If an expedited proposal fails, we do not want to update
	// 	// the deposit at this point since the proposal is converted to regular.
	// 	// As a result, the deposits are either deleted or refunded in all cases
	// 	// EXCEPT when an expedited proposal fails.
	// 	if !(proposal.Expedited && !passes) {
	// 		if burnDeposits {
	// 			err = keeper.DeleteAndBurnDeposits(ctx, proposal.Id)
	// 		} else {
	// 			err = keeper.RefundAndDeleteDeposits(ctx, proposal.Id)
	// 		}

	// 		if err != nil {
	// 			return false, err
	// 		}
	// 	}

	// 	err = keeper.ActiveProposalsQueue.Remove(ctx, collections.Join(*proposal.VotingEndTime, proposal.Id))
	// 	if err != nil {
	// 		return false, err
	// 	}

	// 	switch {
	// 	case passes:
	// 		var (
	// 			idx    int
	// 			events sdk.Events
	// 			msg    sdk.Msg
	// 		)

	// 		// attempt to execute all messages within the passed proposal
	// 		// Messages may mutate state thus we use a cached context. If one of
	// 		// the handlers fails, no state mutation is written and the error
	// 		// message is logged.
	// 		cacheCtx, writeCache := ctx.CacheContext()
	// 		messages, err := proposal.GetMsgs()
	// 		if err != nil {
	// 			proposal.Status = v1.StatusFailed
	// 			proposal.FailedReason = err.Error()
	// 			tagValue = types.AttributeValueProposalFailed
	// 			logMsg = fmt.Sprintf("passed proposal (%v) failed to execute; msgs: %s", proposal, err)

	// 			break
	// 		}

	// 		// execute all messages
	// 		for idx, msg = range messages {
	// 			handler := keeper.Router().Handler(msg)
	// 			var res *sdk.Result
	// 			res, err = safeExecuteHandler(cacheCtx, msg, handler)
	// 			if err != nil {
	// 				break
	// 			}

	// 			events = append(events, res.GetEvents()...)
	// 		}

	// 		// `err == nil` when all handlers passed.
	// 		// Or else, `idx` and `err` are populated with the msg index and error.
	// 		if err == nil {
	// 			proposal.Status = v1.StatusPassed
	// 			tagValue = types.AttributeValueProposalPassed
	// 			logMsg = "passed"

	// 			// write state to the underlying multi-store
	// 			writeCache()

	// 			// propagate the msg events to the current context
	// 			ctx.EventManager().EmitEvents(events)
	// 		} else {
	// 			proposal.Status = v1.StatusFailed
	// 			proposal.FailedReason = err.Error()
	// 			tagValue = types.AttributeValueProposalFailed
	// 			logMsg = fmt.Sprintf("passed, but msg %d (%s) failed on execution: %s", idx, sdk.MsgTypeURL(msg), err)
	// 		}
	// 	case proposal.Expedited:
	// 		// When expedited proposal fails, it is converted
	// 		// to a regular proposal. As a result, the voting period is extended, and,
	// 		// once the regular voting period expires again, the tally is repeated
	// 		// according to the regular proposal rules.
	// 		proposal.Expedited = false
	// 		params, err := keeper.Params.Get(ctx)
	// 		if err != nil {
	// 			return false, err
	// 		}
	// 		endTime := proposal.VotingStartTime.Add(*params.VotingPeriod)
	// 		proposal.VotingEndTime = &endTime

	// 		err = keeper.ActiveProposalsQueue.Set(ctx, collections.Join(*proposal.VotingEndTime, proposal.Id), proposal.Id)
	// 		if err != nil {
	// 			return false, err
	// 		}

	// 		tagValue = types.AttributeValueExpeditedProposalRejected
	// 		logMsg = "expedited proposal converted to regular"
	// 	default:
	// 		proposal.Status = v1.StatusRejected
	// 		proposal.FailedReason = "proposal did not get enough votes to pass"
	// 		tagValue = types.AttributeValueProposalRejected
	// 		logMsg = "rejected"
	// 	}

	// 	proposal.FinalTallyResult = &tallyResults

	// 	err = keeper.SetProposal(ctx, proposal)
	// 	if err != nil {
	// 		return false, err
	// 	}

	// 	// when proposal become active
	// 	keeper.Hooks().AfterProposalVotingPeriodEnded(ctx, proposal.Id)

	// 	logger.Info(
	// 		"proposal tallied",
	// 		"proposal", proposal.Id,
	// 		"status", proposal.Status.String(),
	// 		"expedited", proposal.Expedited,
	// 		"title", proposal.Title,
	// 		"results", logMsg,
	// 	)

	// 	ctx.EventManager().EmitEvent(
	// 		sdk.NewEvent(
	// 			types.EventTypeActiveProposal,
	// 			sdk.NewAttribute(types.AttributeKeyProposalID, fmt.Sprintf("%d", proposal.Id)),
	// 			sdk.NewAttribute(types.AttributeKeyProposalResult, tagValue),
	// 			sdk.NewAttribute(types.AttributeKeyProposalLog, logMsg),
	// 		),
	// 	)

	// 	return false, nil
	// })
	// if err != nil {
	// 	return err
	// }
	return am.AppModule.EndBlock(ctx)
}

// isProposalWhitelisted checks whether a proposal is whitelisted
func isProposalWhitelisted(ctx sdk.Context, am AppModule, proposal govv1.Proposal) bool {
	messages := proposal.GetMessages()

	// iterate over all the proposal messages
	for _, message := range messages {
		sdkMsg, isLegacyProposal := message.GetCachedValue().(*govv1.MsgExecLegacyContent)
		if isLegacyProposal {
			// legacy gov proposal content
			content, err := govv1.LegacyContentFromMessage(sdkMsg)
			if err != nil {
				continue
			}
			if !am.isLegacyProposalWhitelisted(content) {
				// not whitelisted
				return false
			}
			// not legacy gov proposal content
		} else if !am.isModuleWhiteList(message.TypeUrl) {
			// not whitelisted
			return false
		}
	}
	return true
}

// deleteForbiddenProposal removes proposals that are not whitelisted
func deleteForbiddenProposal(ctx sdk.Context, am AppModule, proposal govv1.Proposal) {
	if isProposalWhitelisted(ctx, am, proposal) {
		return
	}

	// delete the votes related to the proposal calling Tally
	// Tally's return result won't be used in decision if the tokens will be burned or refunded (they are always refunded), but
	// this function needs to be called to delete the votes related to the given proposal, since the deleteVote function is
	// private and cannot be called directly from the overridden app module
	am.keeper.Tally(ctx, proposal)

	am.keeper.DeleteProposal(ctx, proposal.Id)
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
