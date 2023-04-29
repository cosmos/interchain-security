package ante_test

import (
	"testing"

	"github.com/stretchr/testify/suite"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	app "github.com/cosmos/interchain-security/app/consumer-democracy"
	"github.com/cosmos/interchain-security/app/consumer-democracy/ante"
	"github.com/stretchr/testify/require"

	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"
	icstestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
	testutil "github.com/cosmos/interchain-security/testutil/integration"
)

type DemocSetupCallback func(t *testing.T) (
	coord *ibctesting.Coordinator,
	consumerChain *ibctesting.TestChain,
	consumerApp testutil.DemocConsumerApp,
)

type ConsumerDemocracyTestSuite struct {
	suite.Suite
	coordinator   *ibctesting.Coordinator
	consumerChain *ibctesting.TestChain
	consumerApp   testutil.DemocConsumerApp
	setupCallback DemocSetupCallback
}

// NewCCVTestSuite returns a new instance of ConsumerDemocracyTestSuite,
// ready to be tested against using suite.Run().
func NewConsumerDemocracyTestSuite[T testutil.DemocConsumerApp](
	democConsumerAppIniter ibctesting.AppIniter,
) *ConsumerDemocracyTestSuite {
	democSuite := new(ConsumerDemocracyTestSuite)

	democSuite.setupCallback = func(t *testing.T) (
		*ibctesting.Coordinator,
		*ibctesting.TestChain,
		testutil.DemocConsumerApp,
	) {
		t.Helper()
		// Instantiate the test coordinator
		coordinator := ibctesting.NewCoordinator(t, 0)

		// Add single democracy consumer to coordinator, store returned test chain and app.
		democConsumer, democConsumerApp := icstestingutils.AddDemocracyConsumer[T](
			t, coordinator, democConsumerAppIniter)

		// Pass variables to suite.
		return coordinator, democConsumer, democConsumerApp
	}
	return democSuite
}

func (suite *ConsumerDemocracyTestSuite) SetupTest() {
	// Instantiate new test utils using callback
	suite.coordinator, suite.consumerChain,
		suite.consumerApp = suite.setupCallback(suite.T())
}

func setup(t *testing.T) *ConsumerDemocracyTestSuite {
	t.Helper()
	suite := NewConsumerDemocracyTestSuite[*app.App](
		icstestingutils.DemocracyConsumerAppIniter)
	suite.SetT(t)
	suite.SetupTest()

	return suite
}

func TestForbiddenProposalsDecorator(t *testing.T) {
	txCfg := app.MakeTestEncodingConfig().TxConfig

	suite := setup(t)

	accountKeeper := suite.consumerApp.GetTestAccountKeeper()
	mintKeeper := suite.consumerApp.GetTestMintKeeper()

	newAuthParamValue := uint64(128)
	newMintParamValue := sdk.NewDecWithPrec(1, 1) // "0.100000000000000000"

	// Mint MsgUpdateParams
	mintParams := mintKeeper.GetParams(suite.consumerChain.GetContext())
	mintParams.InflationMax = newMintParamValue
	msg_1 := &minttypes.MsgUpdateParams{
		Authority: authtypes.NewModuleAddress(govtypes.ModuleName).String(),
		Params:    mintParams,
	}
	// Auth MsgUpdateParams
	authParams := accountKeeper.GetParams(suite.consumerChain.GetContext())
	authParams.MaxMemoCharacters = newAuthParamValue
	msg_2 := &authtypes.MsgUpdateParams{
		Authority: authtypes.NewModuleAddress(govtypes.ModuleName).String(),
		Params:    authParams,
	}

	testCases := []struct {
		name      string
		ctx       sdk.Context
		msgs      []sdk.Msg
		expectErr bool
	}{
		{
			name: "Allowed legacy param change",
			ctx:  suite.consumerChain.GetContext(),
			msgs: []sdk.Msg{
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					// only subspace and key are relevant for testing
					{Subspace: banktypes.ModuleName, Key: "SendEnabled", Value: ""},
				}),
			},
			expectErr: false,
		},
		{
			name: "Allowed param change",
			ctx:  suite.consumerChain.GetContext(),
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]sdk.Msg{msg_1}),
			},
			expectErr: false,
		},
		{
			name: "Forbidden legacy param change",
			ctx:  suite.consumerChain.GetContext(),
			msgs: []sdk.Msg{
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: ""},
				}),
			},
			expectErr: true,
		},
		{
			name: "Forbidden param change",
			ctx:  suite.consumerChain.GetContext(),
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]sdk.Msg{msg_2}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden legacy param changes in the same msg",
			ctx:  suite.consumerChain.GetContext(),
			msgs: []sdk.Msg{
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					{Subspace: banktypes.ModuleName, Key: "SendEnabled", Value: ""},
					{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: ""},
				}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden param changes in the same msg",
			ctx:  suite.consumerChain.GetContext(),
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]sdk.Msg{msg_1, msg_2}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden legacy param changes in different msg",
			ctx:  suite.consumerChain.GetContext(),
			msgs: []sdk.Msg{
				newParamChangeProposalMsg([]sdk.Msg{msg_1}),
				newParamChangeProposalMsg([]sdk.Msg{msg_2}),
			},
			expectErr: true,
		},
		{
			name: "Allowed and forbidden param changes in different msg",
			ctx:  suite.consumerChain.GetContext(),
			msgs: []sdk.Msg{
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					{Subspace: banktypes.ModuleName, Key: "SendEnabled", Value: ""},
				}),
				newLegacyParamChangeProposalMsg([]proposal.ParamChange{
					{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: ""},
				}),
			},
			expectErr: true,
		},
	}

	for _, tc := range testCases {
		tc := tc

		t.Run(tc.name, func(t *testing.T) {
			handler := ante.NewForbiddenProposalsDecorator(app.IsProposalWhitelisted, app.IsParamChangeWhitelisted, suite.consumerApp.GetKeeperMap(), app.IsModuleWhiteList)

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
