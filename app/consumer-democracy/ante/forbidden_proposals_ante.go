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
		submitProposalMgs, ok := msg.(*govv1.MsgSubmitProposal)
		// if the message is MsgSubmitProposal, check if proposal is whitelisted
		if ok {
			messages := submitProposalMgs.GetMessages()
			isWhitelisted := true

			// iterate over all the proposal messages
			for _, message := range messages {
				sdkMsg, isLegacyProposal := message.GetCachedValue().(*govv1.MsgExecLegacyContent)
				if isLegacyProposal {
					// legacy gov proposal content
					content, err := govv1.LegacyContentFromMessage(sdkMsg)
					if err != nil {
						continue
					}
					if !decorator.isLegacyProposalWhitelisted(content) {
						// not whitelisted
						isWhitelisted = false
						break
					}
					// not legacy gov proposal content
				} else if !decorator.isModuleWhiteList(message.TypeUrl) {
					// not whitelisted
					isWhitelisted = false
					break
				}
			}

			if !isWhitelisted {
				return ctx, fmt.Errorf("tx contains unsupported proposal message types at height %d", currHeight)
			}
		}
	}

	return next(ctx, tx, simulate)
}
