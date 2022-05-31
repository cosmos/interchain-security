package app

import (
	"fmt"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ibcconsumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
)

var validMsgsCCVDisabled = map[string]struct{}{}

// MsgFilterDecorator defines an AnteHandler decorator that enables message
// filtering based on certain criteria.
type MsgFilterDecorator struct {
	ConsumerKeeper ibcconsumerkeeper.Keeper
}

func NewMsgFilterDecorator(k ibcconsumerkeeper.Keeper) MsgFilterDecorator {
	return MsgFilterDecorator{
		ConsumerKeeper: k,
	}
}

func (mfd MsgFilterDecorator) AnteHandle(ctx sdk.Context, tx sdk.Tx, simulate bool, next sdk.AnteHandler) (newCtx sdk.Context, err error) {
	currHeight := ctx.BlockHeight()

	// If the CCV channel has yet been established, then we must only allow certain
	// message types.
	if _, ok := mfd.ConsumerKeeper.GetProviderChannel(ctx); !ok {
		if !hasPreCCVValidMsgs(tx.GetMsgs()) {
			return ctx, fmt.Errorf("tx contains unsupported message types at height %d", currHeight)
		}
	}

	return next(ctx, tx, simulate)
}

func hasPreCCVValidMsgs(msgs []sdk.Msg) bool {
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
