package ante_test

import (
	"testing"

	ibcclienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/authz"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"

	"github.com/cosmos/interchain-security/v4/app/consumer/ante"
	appencoding "github.com/cosmos/interchain-security/v4/app/encoding"
)

func TestDisabledModulesDecorator(t *testing.T) {
	txCfg := appencoding.MakeTestEncodingConfig().TxConfig
	authzMsgExecSlashing := authz.NewMsgExec(sdk.AccAddress{}, []sdk.Msg{&slashingtypes.MsgUnjail{}})
	authzMsgExecEvidence := authz.NewMsgExec(sdk.AccAddress{}, []sdk.Msg{&evidencetypes.MsgSubmitEvidence{}})
	nestedAuthzMsgExecSlashing := authz.NewMsgExec(sdk.AccAddress{}, []sdk.Msg{&authzMsgExecSlashing})

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
		{
			name: "authz MsgExec contain slashing module messages not supported",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				&authzMsgExecSlashing,
			},
			expectErr: true,
		},
		{
			name: "authz MsgExec contain evidence module messages not supported",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				&authzMsgExecEvidence,
			},
			expectErr: true,
		},
		{
			name: "nested authz MsgExec contain slashing module messages not supported",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				&nestedAuthzMsgExecSlashing,
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
