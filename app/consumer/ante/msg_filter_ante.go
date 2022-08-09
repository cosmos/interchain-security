package ante

import (
	"fmt"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
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
	}
)

func NewMsgFilterDecorator(k ConsumerKeeper) MsgFilterDecorator {
	return MsgFilterDecorator{
		ConsumerKeeper: k,
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
