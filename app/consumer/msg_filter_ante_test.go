package app_test

import (
	"fmt"
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctransfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	ibcclienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
)

func TestMsgFilterDecorator(t *testing.T) {
	fmt.Println(sdk.MsgTypeURL(&ibctransfertypes.MsgTransfer{}))
	fmt.Println(sdk.MsgTypeURL(&ibcclienttypes.MsgUpdateClient{}))
}
