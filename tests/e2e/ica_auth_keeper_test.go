package e2e_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	icatypes "github.com/cosmos/ibc-go/v3/modules/apps/27-interchain-accounts/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	"github.com/stretchr/testify/suite"
	"github.com/tendermint/tendermint/crypto"

	"bytes"

	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/cosmos/interchain-security/x/ccv/icamauth/keeper"
	"github.com/cosmos/interchain-security/x/ccv/icamauth/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	tmtypes "github.com/tendermint/tendermint/types"
)

var (
	// TODO: Cosmos-SDK ADR-28: Update crypto.AddressHash() when sdk uses address.Module()
	// https://github.com/cosmos/cosmos-sdk/issues/10225
	//
	// TestAccAddress defines a reusable bech32 address for testing purposes
	TestAccAddress = icatypes.GenerateAddress(sdk.AccAddress(crypto.AddressHash([]byte(icatypes.ModuleName))), ibctesting.FirstConnectionID, TestPortID)
	// TestOwnerAddress defines a reusable bech32 address for testing purposes
	TestOwnerAddress = "cosmos17dtl0mjt3t77kpuhg2edqzjpszulwhgzuj9ljs"
	// TestPortID defines a resuable port identifier for testing purposes
	TestPortID, _ = icatypes.NewControllerPortID(TestOwnerAddress)
	// TestVersion defines a reusable interchainaccounts version string for testing purposes
	TestVersion = string(icatypes.ModuleCdc.MustMarshalJSON(&icatypes.Metadata{
		Version:                icatypes.Version,
		ControllerConnectionId: ibctesting.FirstConnectionID,
		HostConnectionId:       ibctesting.FirstConnectionID,
		Encoding:               icatypes.EncodingProtobuf,
		TxType:                 icatypes.TxTypeSDKMultiMsg,
	}))
)

type ICAAuthKeeperTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	path         *ibctesting.Path
	transferPath *ibctesting.Path
	icaPath      *ibctesting.Path
}

func (s *ICAAuthKeeperTestSuite) providerCtx() sdk.Context {
	return s.providerChain.GetContext()
}

func (s *ICAAuthKeeperTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}

func (suite *ICAAuthKeeperTestSuite) SetupTest() {
	suite.coordinator, suite.providerChain, suite.consumerChain = simapp.NewProviderConsumerCoordinator(suite.T())

	// valsets must match
	providerValUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)
	consumerValUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.consumerChain.Vals)
	suite.Require().True(len(providerValUpdates) == len(consumerValUpdates), "initial valset not matching")
	for i := 0; i < len(providerValUpdates); i++ {
		addr1 := utils.GetChangePubKeyAddress(providerValUpdates[i])
		addr2 := utils.GetChangePubKeyAddress(consumerValUpdates[i])
		suite.Require().True(bytes.Equal(addr1, addr2), "validator mismatch")
	}

	// move both chains to the next block
	suite.providerChain.NextBlock()
	suite.consumerChain.NextBlock()

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	err := suite.providerChain.App.(*appProvider.App).ProviderKeeper.CreateConsumerClient(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
		suite.consumerChain.LastHeader.GetHeight().(clienttypes.Height),
		false,
	)
	suite.Require().NoError(err)
	// move provider to next block to commit the state
	suite.providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesis, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer genesis not found")
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), &consumerGenesis)

	// create path for the CCV channel
	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)

	// update CCV path with correct info
	// - set provider endpoint's clientID
	consumerClient, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer client not found")
	suite.path.EndpointB.ClientID = consumerClient
	// - set consumer endpoint's clientID
	providerClient, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(suite.consumerChain.GetContext())
	suite.Require().True(found, "provider client not found")
	suite.path.EndpointA.ClientID = providerClient
	// - client config
	providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerCtx())
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = providerUnbondingPeriod
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = providerUnbondingPeriod / utils.TrustingPeriodFraction
	consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = consumerUnbondingPeriod
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = consumerUnbondingPeriod / utils.TrustingPeriodFraction
	// - channel config
	suite.path.EndpointA.ChannelConfig.PortID = ccv.ConsumerPortID
	suite.path.EndpointB.ChannelConfig.PortID = ccv.ProviderPortID
	suite.path.EndpointA.ChannelConfig.Version = ccv.Version
	suite.path.EndpointB.ChannelConfig.Version = ccv.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// set chains sender account number
	// TODO: to be fixed in #151
	err = suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.Require().NoError(err)
	err = suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(1)
	suite.Require().NoError(err)

	// create path for the transfer channel
	suite.transferPath = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.transferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointA.ChannelConfig.Version = transfertypes.Version
	suite.transferPath.EndpointB.ChannelConfig.Version = transfertypes.Version

	controllerPortID, err := icatypes.NewControllerPortID(TestOwnerAddress)
	suite.Require().NoError(err)

	// create path for the ica channel
	suite.icaPath = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.icaPath.EndpointA.ChannelConfig.PortID = icatypes.PortID
	suite.icaPath.EndpointB.ChannelConfig.PortID = controllerPortID
	suite.icaPath.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.icaPath.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	suite.icaPath.EndpointA.ChannelConfig.Version = TestVersion
	suite.icaPath.EndpointB.ChannelConfig.Version = TestVersion
}

func (suite *ICAAuthKeeperTestSuite) SetupIBCChannels() {
	suite.StartSetupCCVChannel()
	suite.CompleteSetupCCVChannel()
	suite.SetupTransferChannel()
	suite.SetupICAChannel()
}

func (suite *ICAAuthKeeperTestSuite) StartSetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)

	err := suite.path.EndpointA.ChanOpenInit()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)
}

func (suite *ICAAuthKeeperTestSuite) CompleteSetupCCVChannel() {
	err := suite.path.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = suite.path.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}

func (suite *ICAAuthKeeperTestSuite) SetupTransferChannel() {
	// transfer path will use the same connection as ccv path

	suite.transferPath.EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.transferPath.EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.transferPath.EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.transferPath.EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CompleteSetupCCVChannel returns.
	suite.transferPath.EndpointA.ChannelID = suite.consumerChain.App.(*appConsumer.App).
		ConsumerKeeper.GetDistributionTransmissionChannel(suite.consumerChain.GetContext())

	// Complete TRY, ACK, CONFIRM for transfer path
	err := suite.transferPath.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)

	err = suite.transferPath.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.transferPath.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = suite.transferPath.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}

func (suite *ICAAuthKeeperTestSuite) SetupICAChannel() {
	// ica path will use the same connection as ccv path

	suite.icaPath.EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.icaPath.EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.icaPath.EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.icaPath.EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID
}

// SetupICAPath invokes the InterchainAccounts entrypoint and subsequent channel handshake handlers
func SetupICAPath(path *ibctesting.Path, owner string) error {
	if err := RegisterInterchainAccount(path.EndpointB, owner); err != nil {
		return err
	}

	if err := path.EndpointA.ChanOpenTry(); err != nil {
		return err
	}

	if err := path.EndpointB.ChanOpenAck(); err != nil {
		return err
	}

	if err := path.EndpointA.ChanOpenConfirm(); err != nil {
		return err
	}

	return nil
}

func GetProviderICAApp(chain *ibctesting.TestChain) *appProvider.App {
	app, ok := chain.App.(*appProvider.App)
	if !ok {
		panic("not ica app")
	}

	return app
}

func GetConsumerICAApp(chain *ibctesting.TestChain) *appConsumer.App {
	app, ok := chain.App.(*appConsumer.App)
	if !ok {
		panic("not ica app")
	}

	return app
}

// RegisterInterchainAccount is a helper function for starting the channel handshake
func RegisterInterchainAccount(endpoint *ibctesting.Endpoint, owner string) error {
	portID, err := icatypes.NewControllerPortID(owner)
	if err != nil {
		return err
	}

	channelSequence := endpoint.Chain.App.GetIBCKeeper().ChannelKeeper.GetNextChannelSequence(endpoint.Chain.GetContext())

	if err := GetProviderICAApp(endpoint.Chain).ICAControllerKeeper.RegisterInterchainAccount(endpoint.Chain.GetContext(), endpoint.ConnectionID, owner); err != nil {
		return err
	}

	// commit state changes for proof verification
	endpoint.Chain.NextBlock()

	// update port/channel ids
	endpoint.ChannelID = channeltypes.FormatChannelIdentifier(channelSequence)
	endpoint.ChannelConfig.PortID = portID

	return nil
}

// TestICAAuthKeeperTestSuite runs all the tests within this package.
func TestICAAuthKeeperTestSuite(t *testing.T) {
	suite.Run(t, new(ICAAuthKeeperTestSuite))
}

func (suite *ICAAuthKeeperTestSuite) TestRegisterInterchainAccount() {
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

func (suite *ICAAuthKeeperTestSuite) TestSubmitTx() {
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
