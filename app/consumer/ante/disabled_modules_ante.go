package ante

import (
	"fmt"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/authz"
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
		if hasDisabledModuleMsgs(msg, dmd.prefixes...) {
			return ctx, fmt.Errorf("tx contains message types from unsupported modules at height %d", currHeight)
		}

		// Check if there is an attempt to bypass disabled module msg
		// with authz MsgExec
		if nestedAuthzMsgExecCheck(msg, dmd.prefixes...) {
			return ctx, fmt.Errorf("tx contains message types from unsupported modules at height %d", currHeight)
		}
	}

	return next(ctx, tx, simulate)
}

func nestedAuthzMsgExecCheck(msg sdk.Msg, prefixes ...string) bool {
	msgExec, ok := msg.(*authz.MsgExec)

	if !ok {
		return false
	}

	sdkMsgs, err := msgExec.GetMessages()
	if err != nil {
		return false
	}

	for _, msg := range sdkMsgs {
		if hasDisabledModuleMsgs(msg, prefixes...) {
			return true
		}

		// Check for nested authz msgExec
		_, ok = msg.(*authz.MsgExec)
		if ok {
			if nestedAuthzMsgExecCheck(msg, prefixes...) {
				return true
			}
		}
	}

	return false
}

func hasDisabledModuleMsgs(msg sdk.Msg, prefixes ...string) bool {
	msgType := sdk.MsgTypeURL(msg)

	for _, prefix := range prefixes {
		if strings.HasPrefix(msgType, prefix) {
			return true
		}
	}

	return false
}
