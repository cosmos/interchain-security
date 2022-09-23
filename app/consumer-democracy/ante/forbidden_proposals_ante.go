package ante

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
)

type ForbiddenProposalsDecorator struct {
	IsProposalWhitelisted func(govtypes.Content) bool
}

func NewForbiddenProposalsDecorator(whiteListFn func(govtypes.Content) bool) ForbiddenProposalsDecorator {
	return ForbiddenProposalsDecorator{IsProposalWhitelisted: whiteListFn}
}

func (decorator ForbiddenProposalsDecorator) AnteHandle(ctx sdk.Context, tx sdk.Tx, simulate bool, next sdk.AnteHandler) (newCtx sdk.Context, err error) {
	currHeight := ctx.BlockHeight()

	for _, msg := range tx.GetMsgs() {
		submitProposalMgs, ok := msg.(*govtypes.MsgSubmitProposal)
		//if the message is MsgSubmitProposal, check if proposal is whitelisted
		if ok {
			if !decorator.IsProposalWhitelisted(submitProposalMgs.GetContent()) {
				return ctx, fmt.Errorf("tx contains unsupported proposal message types at height %d", currHeight)
			}
		}
	}

	return next(ctx, tx, simulate)
}
