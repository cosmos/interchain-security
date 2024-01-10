package ante_test

import (
	"testing"

	ibctransfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"

	app "github.com/cosmos/interchain-security/v3/app/democracy"
	"github.com/cosmos/interchain-security/v3/app/democracy/ante"
)

// in SDKv47 parameter updates full params object is required
// either all params can be updated or none can be updated
func TestForbiddenProposalsDecorator(t *testing.T) {
	txCfg := app.MakeTestEncodingConfig().TxConfig

	// here we try to set whatever params exist to their default values
	// the actual parameter setting is not important, what's being tested is the ante handle filter
	// Note: mint params CAN be changed according to WhiteListModule in proposals_whitelisting.go
	updateMintParams := &minttypes.MsgUpdateParams{
		Authority: authtypes.NewModuleAddress(govtypes.ModuleName).String(),
		Params:    minttypes.DefaultParams(),
	}

	// Note: auth params CANNOT be changed according to WhiteListModule in proposals_whitelisting.go
	updateAuthParams := &authtypes.MsgUpdateParams{
		Authority: authtypes.NewModuleAddress(govtypes.ModuleName).String(),
		Params:    authtypes.DefaultParams(),
	}

	testCases := []struct {
		name      string
		ctx       sdk.Context
		msgs      []sdk.Msg
		expectErr bool
	}{
		{
			name: "Allowed param change - mint module",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]sdk.Msg{updateMintParams}),
			},
			expectErr: false,
		},
		{
			name: "Forbidden param change - auth module",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]sdk.Msg{updateAuthParams}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden param changes in the same msg",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]sdk.Msg{updateMintParams, updateAuthParams}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden param changes in different msg",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]sdk.Msg{updateMintParams}),
				newParamChangeProposalMsg([]sdk.Msg{updateAuthParams}),
			},
			expectErr: true,
		},
	}

	for _, tc := range testCases {
		tc := tc

		t.Run(tc.name, func(t *testing.T) {
			handler := ante.NewForbiddenProposalsDecorator(app.IsProposalWhitelisted, app.IsModuleWhiteList)

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

// Only ibctransfertypes.SendEnabled/ReceiveEnabled support legacy proposals for changing params
// Note: see LegacyWhitelistedParams in proposals_whitelisting.go
func TestForbiddenLegacyProposalsDecorator(t *testing.T) {
	txCfg := app.MakeTestEncodingConfig().TxConfig

	testCases := []struct {
		name      string
		ctx       sdk.Context
		msgs      []sdk.Msg
		expectErr bool
	}{
		{
			name: "Allowed legacy param change -- only for ibctransfertypes.SendEnabled/ReceiveEnabled",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					// only subspace and key are relevant for testing
					{Subspace: ibctransfertypes.ModuleName, Key: "SendEnabled", Value: "true"},
				}),
			},
			expectErr: false,
		},
		{
			name: "Forbidden param change",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: ""},
				}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden param changes in the same msg",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					// allowed
					{Subspace: ibctransfertypes.ModuleName, Key: "SendEnabled", Value: "true"},
					// disallowed
					{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: ""},
				}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden param changes in different msg",
			ctx:  sdk.Context{},
			msgs: []sdk.Msg{
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					// disallowed
					{Subspace: banktypes.ModuleName, Key: "SendEnabled", Value: ""},
				}),
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					// allowed
					{Subspace: ibctransfertypes.ModuleName, Key: "SendEnabled", Value: "true"},
				}),
			},
			expectErr: true,
		},
	}

	for _, tc := range testCases {
		tc := tc

		t.Run(tc.name, func(t *testing.T) {
			handler := ante.NewForbiddenProposalsDecorator(app.IsProposalWhitelisted, app.IsModuleWhiteList)

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

// Use ParamChangeProposal
func newLegacyParamChangeProposalMsg(changes []proposal.ParamChange) *govv1.MsgSubmitProposal {
	paramChange := proposal.ParameterChangeProposal{Changes: changes}
	msgContent, err := govv1.NewLegacyContent(&paramChange, authtypes.NewModuleAddress(govtypes.ModuleName).String())
	if err != nil {
		return nil
	}
	msg, _ := govv1.NewMsgSubmitProposal([]sdk.Msg{msgContent}, sdk.NewCoins(), sdk.AccAddress{}.String(), "", "", "")
	return msg
}

func newParamChangeProposalMsg(msgs []sdk.Msg) *govv1.MsgSubmitProposal {
	msg, _ := govv1.NewMsgSubmitProposal(msgs, sdk.NewCoins(), sdk.AccAddress{}.String(), "", "", "")
	return msg
}
