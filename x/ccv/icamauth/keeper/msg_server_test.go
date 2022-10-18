package keeper_test

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	icatypes "github.com/cosmos/ibc-go/v3/modules/apps/27-interchain-accounts/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	"github.com/cosmos/interchain-security/x/ccv/icamauth/keeper"
	"github.com/cosmos/interchain-security/x/ccv/icamauth/types"
)

func (suite *KeeperTestSuite) TestRegisterInterchainAccount() {
	var (
		owner string
	)

	testCases := []struct {
		name     string
		malleate func()
		expPass  bool
	}{
		{
			"success", func() {}, true,
		},
		{
			"failure - port is already bound",
			func() {
				GetProviderICAApp(suite.providerChain).IBCKeeper.PortKeeper.BindPort(suite.providerCtx(), TestPortID)
			},
			false,
		},
		{
			"faliure - owner is empty",
			func() {
				owner = ""
			},
			false,
		},
		{
			"failure - channel is already active",
			func() {
				portID, err := icatypes.NewControllerPortID(owner)
				suite.Require().NoError(err)

				channel := channeltypes.NewChannel(
					channeltypes.OPEN,
					channeltypes.ORDERED,
					channeltypes.NewCounterparty(suite.icaPath.EndpointB.ChannelConfig.PortID, suite.icaPath.EndpointB.ChannelID),
					[]string{suite.icaPath.EndpointA.ConnectionID},
					suite.icaPath.EndpointA.ChannelConfig.Version,
				)

				GetProviderICAApp(suite.providerChain).IBCKeeper.ChannelKeeper.SetChannel(suite.providerCtx(), portID, ibctesting.FirstChannelID, channel)
				GetProviderICAApp(suite.providerChain).ICAControllerKeeper.SetActiveChannelID(suite.providerCtx(), ibctesting.FirstConnectionID, portID, ibctesting.FirstChannelID)
			},
			false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest()
			suite.SetupIBCChannels()
			owner = TestOwnerAddress // must be explicitly changed

			tc.malleate() // malleate mutates test data

			msgSrv := keeper.NewMsgServerImpl(GetProviderICAApp(suite.providerChain).ICAMauthKeeper)
			msg := types.NewMsgRegisterAccount(owner, suite.icaPath.EndpointA.ConnectionID, suite.icaPath.EndpointA.ChannelConfig.Version)

			res, err := msgSrv.RegisterAccount(sdk.WrapSDKContext(suite.providerChain.GetContext()), msg)

			if tc.expPass {
				suite.Require().NoError(err)
				suite.Require().NotNil(res)
			} else {
				suite.Require().Error(err)
				suite.Require().Nil(res)
			}
		})
	}
}

func (suite *KeeperTestSuite) TestSubmitTx() {
	var (
		registerInterchainAccount bool
		owner                     string
		connectionId              string
		icaMsg                    sdk.Msg
	)

	testCases := []struct {
		name     string
		malleate func()
		expPass  bool
	}{
		{
			"success", func() {
				registerInterchainAccount = true
				owner = TestOwnerAddress
				connectionId = suite.icaPath.EndpointA.ConnectionID
			}, true,
		},
		{
			"failure - owner address is empty", func() {
				registerInterchainAccount = true
				owner = ""
				connectionId = suite.icaPath.EndpointA.ConnectionID
			}, false,
		},
		{
			"failure - active channel does not exist for connection ID", func() {
				registerInterchainAccount = true
				owner = TestOwnerAddress
				connectionId = "connection-100"
			}, false,
		},
		{
			"failure - active channel does not exist for port ID", func() {
				registerInterchainAccount = true
				owner = "cosmos153lf4zntqt33a4v0sm5cytrxyqn78q7kz8j8x5"
				connectionId = suite.icaPath.EndpointA.ConnectionID
			}, false,
		},
		{
			"failure - module does not own channel capability", func() {
				registerInterchainAccount = false
				owner = TestOwnerAddress
				connectionId = suite.icaPath.EndpointA.ConnectionID
				icaMsg = &banktypes.MsgSend{
					FromAddress: "source-address",
					ToAddress:   "destination-address",
					Amount:      sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))),
				}
			}, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest()
			suite.SetupIBCChannels()

			icaAppA := GetProviderICAApp(suite.providerChain)
			icaAppB := GetConsumerICAApp(suite.consumerChain)

			tc.malleate() // malleate mutates test data

			if registerInterchainAccount {
				err := SetupICAPath(suite.icaPath, TestOwnerAddress)
				suite.Require().NoError(err)

				portID, err := icatypes.NewControllerPortID(TestOwnerAddress)
				suite.Require().NoError(err)

				// Get the address of the interchain account stored in state during handshake step
				interchainAccountAddr, found := GetProviderICAApp(suite.providerChain).ICAControllerKeeper.GetInterchainAccountAddress(suite.providerCtx(), suite.icaPath.EndpointA.ConnectionID, portID)
				suite.Require().True(found)

				icaAddr, err := sdk.AccAddressFromBech32(interchainAccountAddr)
				suite.Require().NoError(err)

				// Check if account is created
				interchainAccount := icaAppB.AccountKeeper.GetAccount(suite.consumerCtx(), icaAddr)
				suite.Require().Equal(interchainAccount.GetAddress().String(), interchainAccountAddr)

				// Create bank transfer message to execute on the host
				icaMsg = &banktypes.MsgSend{
					FromAddress: interchainAccountAddr,
					ToAddress:   suite.consumerChain.SenderAccount.GetAddress().String(),
					Amount:      sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))),
				}
			}

			msgSrv := keeper.NewMsgServerImpl(icaAppA.ICAMauthKeeper)
			msg, err := types.NewMsgSubmitTx(icaMsg, connectionId, owner)
			suite.Require().NoError(err)

			res, err := msgSrv.SubmitTx(sdk.WrapSDKContext(suite.providerCtx()), msg)

			if tc.expPass {
				suite.Require().NoError(err)
				suite.Require().NotNil(res)
			} else {
				suite.Require().Error(err)
				suite.Require().Nil(res)
			}
		})
	}
}
