package ante

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"

	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
)

type ForbiddenProposalsDecorator struct {
	isLegacyProposalWhitelisted func(govv1beta1.Content) bool
	isModuleWhiteList           func(string) bool
}

func NewForbiddenProposalsDecorator(
	whiteListFn func(govv1beta1.Content) bool,
	isModuleWhiteList func(string) bool,
) ForbiddenProposalsDecorator {
	return ForbiddenProposalsDecorator{
		isLegacyProposalWhitelisted: whiteListFn,
		isModuleWhiteList:           isModuleWhiteList,
	}
}

func (decorator ForbiddenProposalsDecorator) AnteHandle(ctx sdk.Context, tx sdk.Tx, simulate bool, next sdk.AnteHandler) (newCtx sdk.Context, err error) {
	currHeight := ctx.BlockHeight()

	for _, msg := range tx.GetMsgs() {
		// if the message is MsgSubmitProposal, check if proposal is whitelisted
		submitProposalMgs, ok := msg.(*govv1.MsgSubmitProposal)
		if !ok {
			continue
		}

		messages := submitProposalMgs.GetMessages()
		for _, message := range messages {
			if sdkMsg, isLegacyProposal := message.GetCachedValue().(*govv1.MsgExecLegacyContent); isLegacyProposal {
				// legacy gov proposal content
				content, err := govv1.LegacyContentFromMessage(sdkMsg)
				if err != nil {
					return ctx, fmt.Errorf("tx contains invalid LegacyContent")
				}
				if !decorator.isLegacyProposalWhitelisted(content) {
					return ctx, fmt.Errorf("tx contains unsupported proposal message types at height %d", currHeight)
				}
			}
			// not legacy gov proposal content and not whitelisted
			if !decorator.isModuleWhiteList(message.TypeUrl) {
				return ctx, fmt.Errorf("tx contains unsupported proposal message types at height %d", currHeight)
			}
		}
	}

	return next(ctx, tx, simulate)
}
