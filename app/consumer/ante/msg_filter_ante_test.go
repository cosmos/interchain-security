package ante_test

import (
	"testing"

	ibcclienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"

	"github.com/cosmos/interchain-security/v4/app/consumer/ante"
	"github.com/cosmos/interchain-security/v4/app/params"
)

type consumerKeeper struct {
	channelExists bool
}

func (k consumerKeeper) GetProviderChannel(_ sdk.Context) (string, bool) {
	return "", k.channelExists
}

func noOpAnteDecorator() sdk.AnteHandler {
	return func(ctx sdk.Context, _ sdk.Tx, _ bool) (sdk.Context, error) {
		return ctx, nil
	}
}

func TestMsgFilterDecorator(t *testing.T) {
	txCfg := params.MakeTestEncodingConfig().TxConfig

	testCases := []struct {
		name           string
		ctx            sdk.Context
		consumerKeeper ante.ConsumerKeeper
		msgs           []sdk.Msg
		expectErr      bool
	}{
		{
			name:           "valid tx pre-CCV",
			ctx:            sdk.Context{},
			consumerKeeper: consumerKeeper{channelExists: false},
			msgs: []sdk.Msg{
				&ibcclienttypes.MsgUpdateClient{},
			},
			expectErr: false,
		},
		{
			name:           "invalid tx pre-CCV",
			ctx:            sdk.Context{},
			consumerKeeper: consumerKeeper{channelExists: false},
			msgs: []sdk.Msg{
				&banktypes.MsgSend{},
			},
			expectErr: true,
		},
		{
			name:           "valid tx post-CCV",
			ctx:            sdk.Context{},
			consumerKeeper: consumerKeeper{channelExists: true},
			msgs: []sdk.Msg{
				&banktypes.MsgSend{},
			},
			expectErr: false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		t.Run(tc.name, func(t *testing.T) {
			handler := ante.NewMsgFilterDecorator(tc.consumerKeeper)

			txBuilder := txCfg.NewTxBuilder()
			require.NoError(t, txBuilder.SetMsgs(tc.msgs...))

			_, err := handler.AnteHandle(tc.ctx, txBuilder.GetTx(), false, noOpAnteDecorator())
			if tc.expectErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
			}
		})
	}
}
