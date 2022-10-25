package e2e

import (
	"time"

	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	"bytes"
	"testing"

	e2e "github.com/cosmos/interchain-security/testutil/e2e"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"

	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	icahostkeeper "github.com/cosmos/ibc-go/v3/modules/apps/27-interchain-accounts/host/keeper"
	icatypes "github.com/cosmos/ibc-go/v3/modules/apps/27-interchain-accounts/types"
	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

var (
	// TestVersion defines a reusable interchainaccounts version string for testing purposes
	TestVersion = string(icatypes.ModuleCdc.MustMarshalJSON(&icatypes.Metadata{
		Version:                icatypes.Version,
		ControllerConnectionId: ibctesting.FirstConnectionID,
		HostConnectionId:       ibctesting.FirstConnectionID,
		Encoding:               icatypes.EncodingProtobuf,
		TxType:                 icatypes.TxTypeSDKMultiMsg,
	}))
)

// CCVTestSuite is an in-mem test suite which implements the standard group of tests validating
// the e2e functionality of ccv enabled chains.
// Any method implemented for this struct will be ran when suite.Run() is called.
type CCVTestSuite struct {
	suite.Suite
	coordinator       *ibctesting.Coordinator
	providerChain     *ibctesting.TestChain
	consumerChain     *ibctesting.TestChain
	providerApp       e2e.ProviderApp
	consumerApp       e2e.ConsumerApp
	providerClient    *ibctmtypes.ClientState
	providerConsState *ibctmtypes.ConsensusState
	path              *ibctesting.Path
	transferPath      *ibctesting.Path
	icaPath           *ibctesting.Path
	setupCallback     SetupCallback
}

// NewCCVTestSuite returns a new instance of CCVTestSuite, ready to be tested against using suite.Run().
func NewCCVTestSuite(setupCallback SetupCallback) *CCVTestSuite {
	ccvSuite := new(CCVTestSuite)
	ccvSuite.setupCallback = setupCallback
	return ccvSuite
}

// Callback for instantiating a new coordinator, provider/consumer test chains, and provider/consumer app
// before every test defined on the suite.
type SetupCallback func(t *testing.T) (
	coord *ibctesting.Coordinator,
	providerChain *ibctesting.TestChain,
	consumerChain *ibctesting.TestChain,
	providerApp e2e.ProviderApp,
	consumerApp e2e.ConsumerApp,
)

// SetupTest sets up in-mem state before every test
func (suite *CCVTestSuite) SetupTest() {

	// Instantiate new test utils using callback
	suite.coordinator, suite.providerChain,
		suite.consumerChain, suite.providerApp,
		suite.consumerApp = suite.setupCallback(suite.T())

	providerKeeper := suite.providerApp.GetProviderKeeper()
	consumerKeeper := suite.consumerApp.GetConsumerKeeper()

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
	err := providerKeeper.CreateConsumerClient(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
		suite.consumerChain.LastHeader.GetHeight().(clienttypes.Height),
		false,
	)
	suite.Require().NoError(err)
	// move provider to next block to commit the state
	suite.providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesis, found := providerKeeper.GetConsumerGenesis(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer genesis not found")
	consumerKeeper.InitGenesis(suite.consumerCtx(), &consumerGenesis)
	suite.providerClient = consumerGenesis.ProviderClientState
	suite.providerConsState = consumerGenesis.ProviderConsensusState

	// allow MsgSubmitProposal from admin module to be sent through ICA
	hostICAGenesis := icatypes.DefaultHostGenesis()
	hostICAGenesis.Params.AllowMessages = []string{"/interchain_security.ccv.adminmodule.v1.MsgSubmitProposal"}
	icahostkeeper.InitGenesis(suite.consumerChain.GetContext(), suite.consumerApp.GetICAHostKeeper(), hostICAGenesis)

	// create path for the CCV channel
	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)

	// update CCV path with correct info
	// - set provider endpoint's clientID
	consumerClient, found := providerKeeper.GetConsumerClientId(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)

	suite.Require().True(found, "consumer client not found")
	suite.path.EndpointB.ClientID = consumerClient
	// - set consumer endpoint's clientID
	providerClient, found := consumerKeeper.GetProviderClientID(suite.consumerChain.GetContext())
	suite.Require().True(found, "provider client not found")
	suite.path.EndpointA.ClientID = providerClient
	// - client config

	trustingPeriodFraction := suite.providerApp.GetProviderKeeper().GetTrustingPeriodFraction(suite.providerCtx())
	providerUnbondingPeriod := suite.providerApp.GetStakingKeeper().UnbondingTime(suite.providerCtx())
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = providerUnbondingPeriod
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = providerUnbondingPeriod / time.Duration(trustingPeriodFraction)
	consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = consumerUnbondingPeriod
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = consumerUnbondingPeriod / time.Duration(trustingPeriodFraction)
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

	controllerPortID, err := icatypes.NewControllerPortID(authtypes.NewModuleAddress(govtypes.ModuleName).String())
	suite.Require().NoError(err)

	// create path for the ica governance channel
	suite.icaPath = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.icaPath.EndpointA.ChannelConfig.PortID = icatypes.PortID
	suite.icaPath.EndpointB.ChannelConfig.PortID = controllerPortID
	suite.icaPath.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.icaPath.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	suite.icaPath.EndpointA.ChannelConfig.Version = TestVersion
	suite.icaPath.EndpointB.ChannelConfig.Version = TestVersion
}

func (suite *CCVTestSuite) SetupCCVChannel() {
	suite.StartSetupCCVChannel()
	suite.CompleteSetupCCVChannel()
}

func (suite *CCVTestSuite) StartSetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)

	err := suite.path.EndpointA.ChanOpenInit()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)
}

func (suite *CCVTestSuite) CompleteSetupCCVChannel() {
	err := suite.path.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = suite.path.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}

func (suite *CCVTestSuite) SetupTransferChannel() {
	// transfer path will use the same connection as ccv path

	suite.transferPath.EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.transferPath.EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.transferPath.EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.transferPath.EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CompleteSetupCCVChannel returns.
	suite.transferPath.EndpointA.ChannelID =
		suite.consumerApp.GetConsumerKeeper().GetDistributionTransmissionChannel(
			suite.consumerChain.GetContext())

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

func (suite *CCVTestSuite) SetupGovernanceICAChannel() {
	// ica path will use the same connection as ccv path
	suite.icaPath.EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.icaPath.EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.icaPath.EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.icaPath.EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID

	// CCV channel handshake will automatically initiate ICA gov channel handshake on Confirm
	// so ICA gov channel will be on stage INIT when CompleteSetupCCVChannel returns.
	suite.icaPath.EndpointB.ChannelID = "channel-1"

	// Complete TRY, ACK, CONFIRM for ICA path
	err := suite.icaPath.EndpointA.ChanOpenTry()
	suite.Require().NoError(err)

	err = suite.icaPath.EndpointB.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.icaPath.EndpointA.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = suite.icaPath.EndpointB.UpdateClient()
	suite.Require().NoError(err)
}
