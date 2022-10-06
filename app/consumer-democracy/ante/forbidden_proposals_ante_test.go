package ante_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	app "github.com/cosmos/interchain-security/app/consumer-democracy"
	"github.com/cosmos/interchain-security/app/consumer-democracy/ante"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/spm/cosmoscmd"
)

func TestForbiddenProposalsDecorator(t *testing.T) {
	txCfg := cosmoscmd.MakeEncodingConfig(app.ModuleBasics).TxConfig

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
					//only subspace and key are relevant for testing
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

func newParamChangeProposalMsg(changes []proposal.ParamChange) *govtypes.MsgSubmitProposal {
	paramChange := proposal.ParameterChangeProposal{Changes: changes}
	msg, _ := govtypes.NewMsgSubmitProposal(&paramChange, sdk.NewCoins(), sdk.AccAddress{})
	return msg
}
