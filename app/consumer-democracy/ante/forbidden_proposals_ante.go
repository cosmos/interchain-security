package ante

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
)

type ForbiddenProposalsDecorator struct {
	IsProposalWhitelisted func(govv1beta1.Content) bool
}

func NewForbiddenProposalsDecorator(whiteListFn func(govv1beta1.Content) bool) ForbiddenProposalsDecorator {
	return ForbiddenProposalsDecorator{IsProposalWhitelisted: whiteListFn}
}

func (decorator ForbiddenProposalsDecorator) AnteHandle(ctx sdk.Context, tx sdk.Tx, simulate bool, next sdk.AnteHandler) (newCtx sdk.Context, err error) {
	currHeight := ctx.BlockHeight()

	for _, msg := range tx.GetMsgs() {
		submitProposalMgs, ok := msg.(*govv1.MsgSubmitProposal)
		// if the message is MsgSubmitProposal, check if proposal is whitelisted
		message := submitProposalMgs.GetMessages()[0]

		sdkMsg := &govv1.MsgExecLegacyContent{
			Content:   message,
			Authority: authtypes.NewModuleAddress(govtypes.ModuleName).String(),
		}

		content, err := govv1.LegacyContentFromMessage(sdkMsg)
		if err != nil {
			return ctx, err
		}

		if ok {
			if !decorator.IsProposalWhitelisted(content) {
				return ctx, fmt.Errorf("tx contains unsupported proposal message types at height %d", currHeight)
			}
		}
	}

	return next(ctx, tx, simulate)
}
