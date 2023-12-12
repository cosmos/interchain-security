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
		msgTypeURL := sdk.MsgTypeURL(msg)

		if hasDisabledModuleMsgs(msg, dmd.prefixes...) {
			return ctx, fmt.Errorf("tx contains message types from unsupported modules at height %d", currHeight)
		}

		// Check if there is an atempt to bypass disabled module msg
		// with authz MsgExec
		if msgTypeURL == "/cosmos.authz.v1beta1.MsgExec" {
			wrappedMsgs := fetchMsgExecWrapperMsgs(msg)
			for _, wrappedMsg := range wrappedMsgs {
				if hasDisabledModuleMsgs(wrappedMsg, dmd.prefixes...) {
					return ctx, fmt.Errorf("tx contains message types from unsupported modules at height %d", currHeight)
				}
			}
		}
	}

	return next(ctx, tx, simulate)
}

func fetchMsgExecWrapperMsgs(msg sdk.Msg) []sdk.Msg {
	var wrappedMsgs = []sdk.Msg{}

	msgExec, ok := msg.(*authz.MsgExec)

	if !ok {
		return []sdk.Msg{}
	}

	sdkMsgs, err := msgExec.GetMessages()
	if err != nil {
		return []sdk.Msg{}
	}

	wrappedMsgs = append(wrappedMsgs, sdkMsgs...)

	return wrappedMsgs
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
