package app

import (
	"fmt"

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
		if !hasValidMsgs(tx.GetMsgs()) {
			return ctx, fmt.Errorf("tx contains unsupported message types at height %d", currHeight)
		}
	}

	return next(ctx, tx, simulate)
}

func hasValidMsgs(msgs []sdk.Msg) bool {
	for _, msg := range msgs {
		msgType := sdk.MsgTypeURL(msg)
		// TODO: Perform message filtering that only allows certain IBC messages
		// using sdk.MsgTypeURL(msg)

		if _, ok := validMsgsCCVDisabled[msgType]; !ok {
			return false
		}
	}

	return true
}
