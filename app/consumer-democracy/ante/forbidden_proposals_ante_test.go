package ante_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"

	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	app "github.com/cosmos/interchain-security/app/consumer-democracy"
	"github.com/cosmos/interchain-security/app/consumer-democracy/ante"
	"github.com/stretchr/testify/require"
)

func TestForbiddenProposalsDecorator(t *testing.T) {
	txCfg := app.MakeTestEncodingConfig().TxConfig

	testCases := []struct {
		name      string
		ctx       sdk.Context
		msgs      []sdk.Msg
		expectErr bool
	}{
		{
			name: "Allowed param change",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]proposal.ParamChange{
					// only subspace and key are relevant for testing
					{Subspace: banktypes.ModuleName, Key: "SendEnabled", Value: ""},
				}),
			},
			expectErr: false,
		},
		{
			name: "Forbidden param change",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]proposal.ParamChange{
					{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: ""},
				}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden param changes in the same msg",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]proposal.ParamChange{
					{Subspace: banktypes.ModuleName, Key: "SendEnabled", Value: ""},
					{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: ""},
				}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden param changes in different msg",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]proposal.ParamChange{
					{Subspace: banktypes.ModuleName, Key: "SendEnabled", Value: ""},
				}),
				newParamChangeProposalMsg([]proposal.ParamChange{
					{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: ""},
				}),
			},
			expectErr: true,
		},
	}

	for _, tc := range testCases {
		tc := tc

		t.Run(tc.name, func(t *testing.T) {
			handler := ante.NewForbiddenProposalsDecorator(app.IsProposalWhitelisted)

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

func newParamChangeProposalMsg(changes []proposal.ParamChange) *govv1beta1.MsgSubmitProposal {
	paramChange := proposal.ParameterChangeProposal{Changes: changes}
	msg, _ := govv1beta1.NewMsgSubmitProposal(&paramChange, sdk.NewCoins(), sdk.AccAddress{})
	return msg
}
