package ante

import (
	"fmt"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
)

type DisabledModulesDecorator struct {
	prefixes []string
}

func NewDisabledModulesDecorator(disabledModules ...string) DisabledModulesDecorator {
	return DisabledModulesDecorator{prefixes: disabledModules}
}

func (dmd DisabledModulesDecorator) AnteHandle(ctx sdk.Context, tx sdk.Tx, simulate bool, next sdk.AnteHandler) (newCtx sdk.Context, err error) {
	currHeight := ctx.BlockHeight()
	for _, msg := range tx.GetMsgs() {
		msgTypeURL := sdk.MsgTypeURL(msg)

		for _, prefix := range dmd.prefixes {
			if strings.HasPrefix(msgTypeURL, prefix) {
				return ctx, fmt.Errorf("tx contains message types from unsupported modules at height %d", currHeight)
			}
		}
	}

	return next(ctx, tx, simulate)
}
