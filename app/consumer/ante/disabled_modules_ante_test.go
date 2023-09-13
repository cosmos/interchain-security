package ante_test

import (
	"testing"

	ibcclienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	"github.com/stretchr/testify/require"

	evidencetypes "cosmossdk.io/x/evidence/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"

	"github.com/cosmos/interchain-security/v3/app/consumer/ante"
	"github.com/cosmos/interchain-security/v3/app/params"
)

func TestDisabledModulesDecorator(t *testing.T) {
	txCfg := params.MakeTestEncodingConfig().TxConfig

	testCases := []struct {
		name      string
		ctx       sdk.Context
		msgs      []sdk.Msg
		expectErr bool
	}{
		{
			name: "IBC module messages supported",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				&ibcclienttypes.MsgUpdateClient{},
			},
			expectErr: false,
		},
		{
			name: "bank module messages supported",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				&banktypes.MsgSend{},
			},
			expectErr: false,
		},
		{
			name: "evidence module messages not supported",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				&evidencetypes.MsgSubmitEvidence{},
			},
			expectErr: true,
		},
		{
			name: "slashing module messages not supported",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				&slashingtypes.MsgUnjail{},
			},
			expectErr: true,
		},
	}

	for _, tc := range testCases {
		tc := tc

		t.Run(tc.name, func(t *testing.T) {
			handler := ante.NewDisabledModulesDecorator("/cosmos.evidence", "/cosmos.slashing")

			txBuilder := txCfg.NewTxBuilder()
			require.NoError(t, txBuilder.SetMsgs(tc.msgs...))

			_, err := handler.AnteHandle(tc.ctx, txBuilder.GetTx(), false,
				func(ctx sdk.Context, _ sdk.Tx, _ bool) (sdk.Context, error) { return ctx, nil })
			if tc.expectErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
			}
		})
	}
}
