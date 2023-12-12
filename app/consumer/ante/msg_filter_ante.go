package ante

import (
	"fmt"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/authz"
)

type (
	// ConsumerKeeper defines the interface required by a consumer module keeper.
	ConsumerKeeper interface {
		GetProviderChannel(ctx sdk.Context) (string, bool)
	}

	// MsgFilterDecorator defines an AnteHandler decorator that enables message
	// filtering based on certain criteria.
	MsgFilterDecorator struct {
		ConsumerKeeper ConsumerKeeper
		prefixes       []string
	}
)

func NewMsgFilterDecorator(k ConsumerKeeper, disabledModules ...string) MsgFilterDecorator {
	return MsgFilterDecorator{
		ConsumerKeeper: k,
		prefixes:       disabledModules,
	}
}

func (mfd MsgFilterDecorator) AnteHandle(ctx sdk.Context, tx sdk.Tx, simulate bool, next sdk.AnteHandler) (newCtx sdk.Context, err error) {
	currHeight := ctx.BlockHeight()

	// If the CCV channel has not yet been established, then we must only allow certain
	// message types.
	if _, ok := mfd.ConsumerKeeper.GetProviderChannel(ctx); !ok {
		if !hasValidMsgsPreCCV(tx.GetMsgs()) {
			return ctx, fmt.Errorf("tx contains unsupported message types at height %d", currHeight)
		}
	}

	// Check if there is an atempt to bypass disabled module msg
	// with authz MsgExec
	wrapperMsgs := fetchMsgExecWrapperMsgs(tx.GetMsgs())
	if hasDisabledModuleMsgs(wrapperMsgs, mfd.prefixes...) {
		return ctx, fmt.Errorf("tx contains message types from unsupported modules at height %d", currHeight)
	}

	return next(ctx, tx, simulate)
}

func hasValidMsgsPreCCV(msgs []sdk.Msg) bool {
	for _, msg := range msgs {
		msgType := sdk.MsgTypeURL(msg)

		// Only accept IBC messages prior to the CCV channel being established.
		// Note, rather than listing out all possible IBC message types, we assume
		// all IBC message types have a correct and canonical prefix -- /ibc.*
		if !strings.HasPrefix(msgType, "/ibc.") {
			return false
		}
	}

	return true
}

func fetchMsgExecWrapperMsgs(msgs []sdk.Msg) []sdk.Msg {
	var wrapperMsgs = []sdk.Msg{}
	for _, msg := range msgs {
		msgType := sdk.MsgTypeURL(msg)

		if msgType == "/cosmos.authz.v1beta1.MsgExec" {
			msgExec, ok := msg.(*authz.MsgExec)

			// TODO: We should decide to continue checking the other msgs or break the loop
			if !ok {
				continue
			}

			sdkMsgs, err := msgExec.GetMessages()
			if err != nil {
				continue
			}

			wrapperMsgs = append(wrapperMsgs, sdkMsgs...)

		}
	}

	return wrapperMsgs
}

func hasDisabledModuleMsgs(msgs []sdk.Msg, prefixes ...string) bool {
	for _, msg := range msgs {
		msgType := sdk.MsgTypeURL(msg)

		for _, prefix := range prefixes {
			if strings.HasPrefix(msgType, prefix) {
				return true
			}
		}
	}

	return false
}
